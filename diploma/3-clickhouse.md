## Общие слова о системе
ClickHouse -- столбцовая система управления базами данных (СУБД) для онлайн обработки аналитических запросов (OLAP). Которая разрабатывается компанией Яндекс и open-source сообществом.

В этой главе мы займемся спецификацией и верификацией деталей протокола репликации этой системы.

### Распределенность
Модель данных КХ оперирует таблицами. Каждая таблица реализуется определенным движком, который отвечает за механизм хранения данных и процесс обработки клиентских запросов.

КХ поддерживает горизонтальное масштабирование с помощью распределенных шардированных таблиц, которые реализуются движком *Distributed*.

КХ -- отказоустойчивая система, где каждый шард распределенной таблицы независимо реплицируется, протокол репликации инкапсулирован в семействе движков *Replicated*.

### Репликация
Будем рассматривать отдельный шард распределенной таблицы.
* Шард - это набор реплик, поведение которых определяется движком ReplicatedMergeTree
* Вставки в таблицу-шард выполняются блоками
* Вставки выполняются через разные реплики шарда, реплики узнают о вставке на другие узлы через ZooKeeper и скачивают соответсвующий блок напрямую у других реплик, которые в текущий момент имеют связь с ZK
* Для обнаружения "мертвых" реплик, в ZooKeeper хранится эфимерная нода is_active, которая показывет, есть ли у узла связь с ZooKeeper-ом. Будем называть такие реплики *активными*.
* Блоки с данными хранятся в отдельных сортированных файлах, для оптимизации чтения эти файлы нужно сливать между собой.
* Для того, чтобы реплики сходились к одному состоянию, они должны договориться о порядке вставок и слияний, для этого они используют лог апдейтов в ZooKeeper
* Информация о вставке попадает в лог после того, как реплика обработала запрос пользователя и записала данные к себе на диск.
* Слияния назначает (добавляет в лог) реплика-лидер, которая выбирается с помощью ZK.

### Отчистка лога
Бесконечно хранить весь лог апдейтов в ZooKeeper невозможно, нужно лишь поддерживать акутальный хвост, а старые записи, которые все реплики уже обработали, можно удалить.

Мы можем удалить старые команды, которые обработали все реплики, так как существующие реплики их уже никогда не увидят, поскольку они двигают свой итератор только вперед, а новые при старте будут копировать состояние с активных реплик.

Каждая из реплик хранит в ZooKeeper log_pointer, который указывает на последнюю, обработанную репликой, запись. Во время очистки будем удалять из лога записи до минимального log pointer-а активных реплик

Реплика может восстановить связь с ZK и снова стать активной. В этот момент ей надо понять, удалили ли нужные ей записи из лога. Для этого во время очистки лога будем помечать неактивные реплики, для которых мы удалили нужные записи, флагом is_lost в ZooKeeper.

Когда такая реплика снова станет активной, она может понять, надо ли ей копировать состояние с другой реплики или можно просто продолжать выполнять лог.

### Quorum Insert/Select
В обычном режиме реплика подтверждает вставку клиенту после того, как запишет данные только на локальный диск, репликация выполняется асинхронно.

Клиент хочет иметь большую надежность и получать подтверждение о вставке только после синхронной записи на несколько реплик. Для этого в ClickHouse используется режим *кворумных вставок*.

Реплика, на которую прилетела кворумная вставка, создает узел в ZooKeeper, записывает в него себя, после чего добавляет запись о кворумной вставке в лог. Когда другие реплики дойдут до этой записи, то проверят, набрался ли кворум для вставки. Если нет, то они скачают себе соответсвующий блок и присоединятся к кворуму, обновив отвечающий ей узел в ZK.

Если реплика увидит, что в znode для кворума собралось нужное количетсво реплик, то узел удалит эту znode, и запись подтвердится клиенту. Если по какой-то причине реплика, которая хочет принять участие в кворуме, не может получить этот блок, то кворум считается провалившимся и информация об этом записывается в ZooKeeper.

Этот алгоритм можно улучшить, чтобы обеспечить sequential consistency для чтений. Чтобы это добиться надо во время чтения отвечать, только если на реплике есть все блоки, вставлененые с кворумом. Для этого в ZooKeeper хранится номер последнего записанного блока вместе с кворумом.

Когда на реплику приходит Select, то реплика отвечает на него, только если у нее есть все блоки, которые быди вставлены с кворумом, кроме тех, для которых провалился кворум.

## Моделирование
В первую очередь выберем уровень абстракции для модели.

Во время апдейта (вставка или слияние) реплика первым делом вставляет информацию о нем в ZooKeeper. Таким образом, все действия над системой упорядочиваются с помощью лога и информацию о новых апдейтах и порядок на них реплики получают именно из него, поэтому, в отличие от Kafka, нам не надо моделировать общение между репликами, а можно считать, что если реплика прочитала информацию о вставке, то она сразу скачала себе этот кусок данных.

Основными действующими лицами будут реплики и клиены. Для лучшей читаемости объединим действия для каждой из сущностей:

    ReplicaAction ==
        \E replica \in Replicas:
            \/ ExecuteInsert(replica)
            \/ ExecuteMerge(replica)
            \/ BecomeLeader(replica)

    ClientAction ==
        \/ Insert
        \/ Select

Реплики могут рестартовать или терять связность с другими репликами и ZK (например, если реплика находится в ДЦ, недоступном из-за повреждения канала). Моделировать это будем с помощью действий ReplicaBecomeInactive и ReplicaBecomeActive:


    ReplicaBecomeInactive ==
        /\ \E replica \in Replicas :
          /\ IsActive(replica)
          /\ RepicaStartInactive(replica)
          ...

    ReplicaBecomeActive ==
        /\ \E replica \in Replicas :
          /\ ~IsActive(replica)
          /\ RepicaStartActive(replica)
          ...

Вся информация о реплике хранится (флаг is_active, log_pointer, локальные куски и т.д.) в отдельном узле в ZK. После рестарта реплика должна восстановить, какие записи из лога она уже успела обработать и какие куски у нее есть локально.

Недетерминизм в системе проявляется в нескольких моментах:

Клиент может отправить свой запрос на любую из реплик. Отправку запросов мы моделируем с помощью действия:

    QuorumReadLin ==
        ...
        /\ \E replica \in Replicas :
            /\ IsActive(replica)
            /\ Cardinality(GetCommitedId) = Cardinality(replicaState[replica].local_parts \ ({quorum.data} \cup GetData(failedParts)))
        ...

    ClientAction ==
        \/ QuorumInsert
        \/ QuorumReadLin

Во-вторых, любая из реплик может совершить действие по собственной инициативе: отказать, обработать новую запись в логе, обновить информацию о кворуме. Поведение реплики мы моделируем с помощью действия ReplicaAction:


     ReplicaAction ==
         \E replica \in Replicas:
          \/ IsActive(replica)
              /\ \/ ExecuteLog(replica)
                 \/ UpdateQuorum(replica)
                 \/ EndQuorum(replica)
                 \/ BecomeInactive(replica)
                 \/ FailedQuorum(replica)
          \/ ~IsActive(replica)
              /\ BecomeActive(replica)

### Тестирование
Верификация подтверждает корректность алгроитма обрезки лога: инвариант ValidLogPointer не нарушается:

    ValidLogPointer == [] (\A replica \in Replicas: IsActive(replica) => deletedPrefix < replicaState[replica].log_pointer)

Отдельного внимания заслуживает спека про Кворумы.

В КХ есть настрока sequential_consistency, которая должна обеспечивать один из режимов согласованнорсти.

При таком режиме реплика отвечает на запрос пользователя, когда у нее максимальный номер локального последнего вставленного блока равен номеру последнего блока, вставленного с помощью кворумных вставок, который читается из ZK. Чтения, в ZK в отличие от записей, не проходят через протокол ZAB, а выполняются локально. Это означает, что мы могли получить устаревшее значение для последней кворумной записи.

    QuorumReadWithoutLin ==
        /\ Len(log) > 0
        /\ Cardinality(GetSelectFromHistory(history)) < HistoryLength
        /\ \E replica \in Replicas :
            /\ IsActive(replica)
            /\ LET max_data == Max(replicaState[replica].local_parts \ ({quorum.data} \cup GetData(failedParts)))
               IN /\ max_data # NONE
                  /\ ReadEvent(GetIdForData(max_data, log))
        /\ UNCHANGED <<log, replicaState, nextRecordData, quorum, lastAddeddata, failedParts>>

Если проверить историю, то TLC выдаст ошибку.

Если в ZK сделать линеаризуемое чтение, то и сам КХ тоже будет линеаризуем для кворумных чтений. Промоделируем это с помощью экшена QuorumReadLin:

    QuorumReadLin ==
        /\ Len(log) > 0
        /\ Cardinality(GetSelectFromHistory(history)) < HistoryLength
        /\ \E replica \in Replicas :
            /\ IsActive(replica)
            /\ Cardinality(GetCommitedId) = Cardinality(replicaState[replica].local_parts \ ({quorum.data} \cup GetData(failedParts)))
            /\ LET max_data == Max(replicaState[replica].local_parts \ ({quorum.data} \cup GetData(failedParts)))
               IN /\ max_data # NONE
                  /\ ReadEvent(GetIdForData(max_data, log))
        /\ UNCHANGED <<log, replicaState, nextRecordData, quorum, lastAddeddata, failedParts>>

Если проверить историю с таким экшеном, то она получается линеаризуемой.
