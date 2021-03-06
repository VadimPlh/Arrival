# Часть 2 (model checker)
В предыдущей главе мы исследовали техники моделирования распределенных систем с помощью TLA+. В этой главе мы поговорим про верификацию модели с помощью TLC - model checker-а для TLA+

TLC явно исследует граф состояний системы: для проверки инвариантов ему нужно обойти каждое достижимое состояние, а для проверки произвольных темпоральных свойств – явно разложить весь граф в памяти и найти в нем сильно связные компоненты.

## Масштаб модели
Для формальной верификации модели в ней нужно зафиксировать значения параметров, отвечающих конкурентной активности: число реплик в распределенной системе, число proposal-ов в Single-Decree Paxos, число транзакций в Percolator и т.д. Эти параметры ограничивают число состояний модели и делают ее пригодной для model checking-а.

Нетрудно заметить, что число состояний модели будет экспоненциально зависеть от значений этих параметров. А значит мы не сможем позволить себе тот же масштаб конкурентности, что и в реальной системе.

Тем не менее, проверка модели даже для небольших значений параметров все же может убежать в корректности. Природа конкурентных багов такова, что они хоть и могут требовать большого числа шагов, но как правило моделируются на небольшом числе узлов / потоков / транзакций. Поэтому можно ожидать, что если существует исполнение, которое нарушает свойства, то оно будет представлено.

Приведем примеры, подтверждающие эту интуицию:
* В Basic Paxos аксепта одного и того же значения на большинстве acceptor-ов недостаточно для того, чтобы значение считалось выбранным - контрпример можно построить на 3-х аcceptor-ах и 4-х proposal-ах.
* Баги в lf алгоритмах чаще всего можно промоделировать на очень небольшом числе потоков, независимо от сложности самого бага.
* Read-only аномалия в алгоритме Snapshot Isolation достигается на 3-х транзакциях и 2-х ключах.
* Авторы статьи "https://www.usenix.org/system/files/conference/osdi14/osdi14-paper-yuan.pdf" изучили 198 сбоев в 5 распределенных системах (Cassandra, HBase, HDFS, Hadoop MapReduce и Redis) и обнаружили, что: "Almost all (98%) of the failures are guaranteed to manifest on no more than 3 nodes. 84% will manifest on no more than 2 nodes…. It is not necessary to have a large cluster to test for and reproduce failures".

На практике для верификации распределенных алгоритмов достаточно < 10 участников: реплик / proposal-ов / транзакций.

## Исследование графа
TLC может исследовать граф состояний системы двумя способами: с помощью обхода в ширину и с помощью симуляции.

По умолчанию TLC использует поиск в ширину. Поиск в ширину гарантирует, что при нарушении инварианта чекер выдаст контпример минимальной длины.

Например, TLC находит более короткий сценарий Read-only аномалии в алогритме Snapshot Isolation, чем в оригинальной статье про эту аномалию.

Обход графа состояний в ширину позволяет проверять модели с бесконечным числом состояний: все возможные траектории будут исследованы "параллельно". Значит чем дольше  model checker исследует нашу спеку, тем больше можно быть увереным, что тем больше наша уверенность в корректности моделируемой системы.

Но если мы знаем, что короткого контрпримера нет, то можно попытать удачу в режиме симуляции: вместо исследования сразу всех траекторий чекер будет выбирать произвольные.

Например, этот способ позволяет найти сценарий read-only аномалии в SI гораздо быстрее, чем обход в ширину.

## Дедлоки
Чтобы ограничить число состояний в модели для исследуемой системы, мы ограничиваем число клиентских операций / транзакций, а значит в модели возникают состояния, в которой все события уже произошли и никаких переходов сделать уже нельзя.

TLC по умолчанию примет эти состояния за дедлок алгоритма, хотя они говорят лишь о конце работы системы.

Чтобы избавиться от "ложных" дедлоков, заведем дополнительный дизъюнкт в Next, который будет порождать явную петлю в состояниях, в которых исчерпаны ограниченные внешние события (запросы клиентов, транзакции и т.п.).

Например, в спеке SI добавляется в Next новый экшен, где проверяется, что id завершенных транзакций совпадают с начальным набором:

    LegitimateTermination ==  FinalizedTxns(history) = TxnId

    Next == \/ \E txn \in TxnId :
                \/ Begin(txn)
                \/ Commit(txn)
                \/ ChooseToAbort(txn) (* as contrasted with being forced to abort by FCW rule or deadlock prevention *)
                \/ \E key \in Key :
                    \/ Read(txn, key)
                    \/ StartWriteMayBlock(txn, key)

                   (* Internal actions *)
                \/ FinishBlockedWrite(txn)
            \/ (LegitimateTermination /\ UNCHANGED allvars)

## Тестирование
Хотя спецификация системы в TLA+ и является логической формулой, к ней применимы критерии качества (единый стиль, комментарии к сложным действиям) и техники работы (тестирование отдельных операторов и проверка покрытия "кода" спеки) с программным кодом.

### Юнит-тестирование
Полезно писать юнит-тесты для отдельных нетривиальных операторов из которых потом строятся свойства.

Примеры:

В спеке SI юнит тесты проверяют, что оператор FindAllNodesInAnyCycle обнаруживает цикл в графе конфликтующих транзакций.

    UnitTests_FindAllNodesInAnyCycle ==
        /\ FindAllNodesInAnyCycle({})                                                       = {}
        /\ FindAllNodesInAnyCycle({<<"a", "b">>})                                           = {}
        /\ FindAllNodesInAnyCycle({<<"a", "b">>, <<"b", "c">>, <<"c", "d">>})               = {}
        ...

Следующие тесты проверяют, что спецификация пораждает валидные истории исполнения транзакций: каждая транзакция в истории должна проходить через шаги Begin -> [Write|Read] -> Abort|Commit.

    UnitTest_WellFormedTransactionsInHistory ==
             (* must begin *)
        /\   WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"]>>)
        /\ ~ WellFormedTransactionsInHistory(<<[op |-> "write", txnid |-> "T_1", key |-> "K_X"], [op |-> "begin", txnid |-> "T_1"]>>)
             (* multiple begin *)
        /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "begin", txnid |-> "T_1"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"]>>)
        ...

"Запустить" тесты можно так:
 1) В секции TLC "What is the behavior spec?", выбрать "No Behavior Spec"
 2) В "Evaluate Constant Expression" написать название юнит-теста

### Покрытие кода
Если TLC не нашел нарушения свойств, то полезно убедиться, что он при этом действительно исследовал нетривиальные поведения системы и использовал все описанные действия. Иначе говоря, полезно проверить покрытие "кода" спеки.

Например:
* В SI можно проверить, что транзакции вообще начинаются и некоторые выполняются. Так как только тогда можно говорить о каких-нибудь свойствах.
* В Paxos можно проверить, что вторая фаза алгоритма вообще происходит.

Для того, чтобы проверить наличие нетривиальной траектории, нужно написать инвариант, который будет выделять ее, и проверить его отрицание.

Пример:

Алгоритм изоляции транзакций SI не гарантирует сериализуемости, он может порождать аномалии -- исполнения, которые нельзя сериализовать. Так что помимо свойств, которые этот алгоритм обеспечивает, разумно проверить, что в модели, которую исследовал TLC, эти аномалии действительно были.

    ReadOnlyAnomaly(h) ==
            (* current history is not serializable *)
        /\  ~ CahillSerializable(h)
            (* and there is a transaction that does some reads and zero writes,
               and when that transaction is entirely removed from the history,
                   the resulting history is serializable. *)
        /\ \E txn \in TxnId :
                LET keysReadWritten == KeysReadAndWrittenByTxn(h, txn)
                IN
                    /\ Cardinality(keysReadWritten[1]) > 0
                    /\ Cardinality(keysReadWritten[2]) = 0
                    /\ CahillSerializable(HistoryWithoutTxn(h, txn))

Разработчик TLC работает над встроенным профилированием в IDE, что упрости проверку покрытия кода.

### Мутационоое тестирование
Мутационное тестирование – способ удостовериться в качестве сигнала об успешно пройденных тестах. При мутационном тестировании в программу вносятся небольшие деструктивные изменения, которые должны сломать тесты. Если этого не произошло, то тесты необходимо переделать.

Аналогично с формальной верификацией: в спецификацию алгоритма вносятся ошибки, после чего TLC должен обнаружить нарушения свойств.

Алгоритм Paxos построен на том, что кворум первой фазы алгоритма пересекается с кворумов второй фазы. Если при проверке модели задать систему кворумов, в которой есть два непересекающихся множества, то TLC должен обнаружить нарушение свойства SafeValue.

### Проверка типов
Подобно динамически типизированным языкам программирования, переменные в TLA+ не имеют типов. Вот что пишет по этому поводу Лэмпорт: "If a specification language is to be general, it must be expressive. No simple type system is as expressive as untyped set theory. While a simple type system can allow many specifications to be written easily, it will make some impossible to write and others more complicated than they would be in set theory."

Но у выразительности есть обратная сторона, хорошо знакомая разработчикам на динамически-типизированных ЯП: простая опечатка в тексте программы может проявиться только во время запуска и далеко не сразу. То же справедливо и для TLA+.

Чтобы отлаживать подобные ошибки, полезно ввести технический инвариант, который будет проверять, что переменные, которые образуют состояние системы, принимают ожидаемые значения.

По положенной Лэмпортом традиции такой инвариант называют TypeOK.

Примеры:

Paxos:

    Message ==      [type : {"1a"}, bal : Ballot]
               \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
                     mbal : Ballot \cup {-1}, mval : Value \cup {None}]
               \cup [type : {"2a"}, bal : Ballot, val : Value]
               \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

    TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
              /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
              /\ maxVal \in [Acceptor -> Value \cup {None}]
              /\ msgs \subseteq Message

Как правило в TypeOk описан сетевой протокол, то есть все возможные сообщения, которыми могут обмениваться узлы.

## Читаемая траектория
TLC умеет печатать траекторию, на которой нарушились проверяемые свойства. Траектория представляет собой либо конечную последователь состояний, либо цикл состояний (при нарушении темпоральных свойств). Каждое состояние описывается значениями переменных.

Чтобы в траектории для каждого состояния был указано действие, который был взят при переходе, Next должен представлять собой простую дизъюнкцию:

Пример: Kafka

    Next ==
        \/ ControllerElectLeader
        \/ ControllerShrinkIsr
        \/ BecomeLeader
        \/ LeaderExpandIsr
        \/ LeaderShrinkIsr
        \/ LeaderWrite
        \/ LeaderIncHighWatermark
        \/ BecomeFollowerTruncateToHighWatermark
        \/ FollowerReplicate

Такой подход требует, что бы мы внесли квантор существования в каждое отдельное действие, что ухудшает читаемость.

Если же внести все действия одной сущности под один квантор существования, то мы потеряем ссылки на действия в траектории:

    Next == \/ \E b \in Ballot : \/ Phase1a(b)
                                 \/ \E v \in Value : Phase2a(b, v)
            \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Надо сдедать выбор между читаемостью траектории и читаемостью спеки.
