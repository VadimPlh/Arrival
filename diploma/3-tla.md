# Часть 3 (TLA+)
## Тестирование
Хоть описание системы происходит с помощью языка математики, и спека является логической формулой, все равно стоит задумываться о тестировании и чистоте написания кода. Важно использовать единый кодстайл, как и влюбом другом коде, тестировать каждую часть спеки, так как найти ошибку в формальном описании довольно сложно.

### Unit tests
Полезно писать юнит-тесты для ваших операторов.
Пример:

В спеке SI юнит тесты проверяют, что FindAllNodesInAnyCycle обнаруживает цикл в конфликтующих транзакций, если такие циклы есть, то история не будет сериализуемой.

    UnitTests_FindAllNodesInAnyCycle ==
        /\ FindAllNodesInAnyCycle({})                                                       = {}
        /\ FindAllNodesInAnyCycle({<<"a", "b">>})                                           = {}
        /\ FindAllNodesInAnyCycle({<<"a", "b">>, <<"b", "c">>, <<"c", "d">>})               = {}                   (* no cycle, more nodes *)
        /\ FindAllNodesInAnyCycle({<<"a", "a">>})                                           = {"a"}                (* cycle of length 1 *)
        /\ FindAllNodesInAnyCycle({<<"a", "b">>, <<"b", "a">>})                             = {"a", "b"}           (* cycle of length 2 *)
        /\ FindAllNodesInAnyCycle({<<"a", "b">>, <<"b", "c">>, <<"c", "d">>, <<"d", "a">>}) = {"a", "b", "c", "d"} (* cycle of length 3 *)
        /\ FindAllNodesInAnyCycle({<<"a", "a">>, <<"b", "b">>})                             = {"a", "b"}           (* multiple disjoint cycles of length 1*)
        /\ FindAllNodesInAnyCycle({<<"a", "d">>, <<"d", "b">>, <<"c", "d">>, <<"d", "c">>}) = {"d", "c"}           (* cycles plus some nodes not in any cycle but which join to a cycle *)
        /\ FindAllNodesInAnyCycle({<<"a", "b">>, <<"b", "a">>, <<"c", "c">>, <<"d", "c">>}) = {"a", "b", "c"}      (* multiple disjoint cycles including length > 1 *)

Эти юнит тесты проверяют, что WellFormedTransactionsInHistory обнаруживает, что последовательность операций в любой транзакции имеет вид: Begin -> Writes/Reads -> Abort/Commit

    UnitTest_WellFormedTransactionsInHistory ==
             (* must begin *)
        /\   WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"]>>)
             (* just begin & commit *)
        /\   WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "commit", txnid |-> "T_1"]>>)
             (* begin, readX, writeY, commit *)
        /\   WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "read", txnid |-> "T_1", key |-> "K_X", ver |-> "T_2"], [op |-> "write", txnid |-> "T_1", key |-> "K_Y"], [op |-> "commit", txnid |-> "T_1"]>>)
             (* begin, readX, writeX, abort *)
        /\   WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "read", txnid |-> "T_1", key |-> "K_X", ver |-> "T_2"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"], [op |-> "abort", txnid |-> "T_1", reason |-> "voluntary"]>>)
        (* Negative tests *)
             (* begin out of place *)
        /\ ~ WellFormedTransactionsInHistory(<<[op |-> "write", txnid |-> "T_1", key |-> "K_X"], [op |-> "begin", txnid |-> "T_1"]>>)
             (* multiple begin *)
        /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "begin", txnid |-> "T_1"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"]>>)
             (* commit out of place (after a begin of a different transaction) *)
        /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "commit", txnid |-> "T_1"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"]>>)
             (* abort out of place *)
        /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "abort", txnid |-> "T_1", reason |-> "voluntary"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"]>>)
             (* Violation of Bernstein's simplification: multiple writes to same key *)
        /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"]>>)
             (* Violation of Bernstein's simplification: multiple reads of same key *)
        /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "read", txnid |-> "T_1", key |-> "K_X", ver |-> "T_2"], [op |-> "read", txnid |-> "T_1", key |-> "K_X", ver |-> "T_2"]>>)

"Запустить" их можно так:
 1) В секции TLC "What is the behavior spec?", выбрать "No Behavior Spec"
 2) В "Evaluate Constant Expression" написать название юнит-теста

### Поиск поведения
После написания спеки надо удостовериться, что в ней существую нетривиалные траектории, которые захватывают наиболее важные для нас экшены.

Например:
* В SI можно проверить, что транзакции вообще начинаются и некоторые выполняются. Так как только тогда можно говорить о каких-нибкдь св-вах
* В Paxos можно проверить, что вторая фаза алгоритма вообще происходит.

Это можно сделать просто написав св-во, которое будет верно только для этого плохого поведения.

Например, в спеке про репликацию в КХ можно проверить, что мерджи назначаются. Для этого будем проверять, что в любом поведении нет мерджей

DoNotMerge == [](\A record \in Range(log): record.type != "Merge").

Дальше надо model checker запустить c проверкой этого св-ва, и если все реализовано правильно, то TLC выдаст нам траекторию, где такого не проиходит. А она, в свою очередь, будет гарантировать, что экшен будет взят.

Аналогично можно поступить, когда надо понять, что генерируется необычная последовательность событий. Для этого достаточно написать предикат, которому удовлетворяет наше поведение.

Пример: в спеке SI автор ищет поведения, которые удовлетворяют ReadOnlyAnomaly.

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

Тесты для нашей спецификации можно оценить с помощью метрики "покрытие кода". Надо удостовериться, что все экшены будут взяты. Все операторы работаю правильно.

### Мутационоое тестирование
Мутационное тестирование (мутационный анализ или мутация программ) — это метод тестирования программного обеспечения, который включает небольшие изменения кода программы. Если набор тестов не в состоянии обнаружить такие изменения, то он рассматривается как недостаточный.

Суть мутационного тестирования в том, чтобы изменить произволную часть алогритма и проверить, что тесты смогут это обнаружить.

Например: в спеке FPaxos можно изменить системы кворумов. На второй фазе MCQuorum2 == {{a1, a3},{a2, a4}} -> {{a1},{a2, a4}}. После этого надо запустить провреку и увидим, что у нас нарушилось св-во *SafeValue*, так как алгоритм Паксоса построен на том, что кворум из первый фазы точно пересечется с кворумом из второй фазы хотя бы по одному acceptor-у, и тем самым будет обнаружено ранее предложенное значение. (для работы надо удалить ASSUME). А мы убрали этот инвариант и алгоритм смог принять 2 значения.

Подобные ограничения в TLA формулируют в виде assumption.

Например:
FPaxos

    ASSUME QuorumAssumption == /\ \A Q \in Quorum1 : Q \subseteq Acceptor
                            /\ \A Q \in Quorum2 : Q \subseteq Acceptor
                            /\ \A Q1 \in Quorum1 : \A Q2 \in Quorum2 : Q1 \cap Q2 # {}

Kafka

    ASSUME
        /\ None \notin Replicas
        /\ MaxLeaderEpoch \in Nat

## TypeOk
*В TLA+ использует нетипизированную теорию мн-в, создатель TLA+ Лампорт в своей статье ["Should Your Specification Language Be Typed?"](https://lamport.azurewebsites.net/pubs/lamport-types.pdf) описывает, почему он сделал такой выбор. Лампорт в TLA+ не выбрал строго-типизированный язык, так как проверка типов может создать излишнюю сложность при написании формальной спецификации. Языки программирования используют типы для проверки на стадии компиляции. Строгие типы помогают отловить класс ошибок, которые могут произойти во время работы программы, но они сильно усложняют язык и накладывают ограничения.*
TLA+ использует теорию мн-в вместе с проверкой типов, что создаст дополнительное условие для проверки TLC и помогает отловить класс ошибок.

"If a specification language is to be general, it must be expressive. No simple type system is as expressive as untyped set theory. While a simple type system can allow many specifications to be written easily, it will make some impossible to write and others more complicated than they would be in set theory."

Полезно ввести технический инвариант, который будет проверять не свойства системы, а корректность модели – что значения переменных, которые образуют состояния системы, принимают значения определенного типа, который мы используем в реализации.

Как правило в TypeOk описан сетевой протокол, то есть все возможные сообщения, которыми могут обмениваться ноды:

Paxos:

    Message ==      [type : {"1a"}, bal : Ballot]
               \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
                     mbal : Ballot \cup {-1}, mval : Value \cup {None}]
               \cup [type : {"2a"}, bal : Ballot, val : Value]
               \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

Raft:

    ReplicaState == [hw : ReplicaLog!Offsets \union {LogSize},
                     leaderEpoch: LeaderEpochOpt,
                     leader : ReplicaOpt,
                     isr: SUBSET Replicas]

Примеры TypeOk:
SI

    TypeInv ==  /\ history            \in Seq(EventsT)
                   (* A transaction may hold indepedent exclusive locks on any number of keys *)
                /\ holdingXLocks      \in [TxnId -> SUBSET Key]
                   (* A transaction can be waiting for at most one exclusive lock *)
                /\ waitingForXLock    \in [TxnId -> Key \union {NoLock}]
                /\ inConflict         \in [TxnId -> BOOLEAN]
                /\ outConflict        \in [TxnId -> BOOLEAN]
                /\ holdingSIREADlocks \in [TxnId -> SUBSET Key]
Kafka

    TypeOk ==
        /\ LeaderEpochSeq!TypeOk
        /\ RecordSeq!TypeOk
        /\ ReplicaLog!TypeOk
        /\ replicaState \in [Replicas -> ReplicaState]
        /\ quorumState \in QuorumState
        /\ leaderAndIsrRequests \subseteq QuorumState
Paxos

    TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
              /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
              /\ maxVal \in [Acceptor -> Value \cup {None}]
              /\ msgs \subseteq Message

Для пользовательских структур надо определить тип для каждого поля из структуры. Для этого надо сгенерировать все возможные значения, которые может принимать ваша структура (Это делается [a: {...}, b: {2, 3}, ...], такая запись генерирует мн-во со всеми возможными значениями. Если одно из значений не мн-во, то стоит использовать "->" [a -> 1, b: {2, 3}, ...]). В инварианте проверять, что переменная \in во всех возможных значениях

## Бесконечная и конечная спека
Кол-во возможных состояний у распределенной системы - б.м., так как мы не говорим о ее завершении. От model checker-а ожидают разумное время на проверку нашей спеки, для этого надо сделать возможное кол-во состояний конечным, для этого надо ограничить возможное число действий системы конечным числом или узлов, которые принимают участие в алгоритме.

Примеры:

В Kafa-е ограничивается кол-во реплик и кол-во запросов от клиента.

    CONSTANTS
        Replicas,
        LogSize,
        MaxRecords,
        MaxLeaderEpoch

В SI ограничивают кол-во возможныз транзакций в алгоритме.

    CONSTANTS TxnId, Key


Мы могли получить состояние, откуда не бывает перехода в другой экшен, так как все события уже произошли. Если запустить TLC, то он найдет состояние, из которого нет перенхода в другие, в терминах TLC  - это дедлок.  Мы ограничили кол-во событий, которые могут произойти в системе, тем самым мы создали состояние, из которого нет переходов в другие, но оно не означает дедлок алгоритма, а говорит только о конце действий система. Лампорт пишет: "A deadlock is said to occur in a state for which the next-state relation allows no successor states.  Termination is deadlock that is not considered an error.  If you want the behavior spec to allow termination, then you should uncheck the deadlock option." Но никто не хочет отключать одну из важных проверок для системы, поэтому воспользуемся приемом из спеки SI.

Чтобы избежать “ложных” срабатываний, заведем дополнительный дизъюнкт в Next, который будет порождать явную петлю в состояниях, в которых исчерпаны ограниченные нами внешние события: клиентские запросы / транзакциии / proposal-ы, таким образом мы избавимся от технического дедлока.

Пример в [SI]:

    LegitimateTermination ==  FinalizedTxns(history) = TxnId

## BFS/simulation
В обычном TLC использует явную проверку моделей: исследует весь граф состояний системы с помощью обхода в ширину.  Для проверки инвариантов во время обхода каждое состояние проверяется на удовлетворение написанным св-вам. Иногда не надо полностью исследовать граф састояний, а достаточно найти какое-то интересное поведение.

Чекер используя BFS обходит граф конфигураций системы и проверяет св-ва. В чем + такого обхода - если  model checker находит обишку, то он выдает контрпример минимальной длины - это нам гарантирует BFS.

Пример: В [презентации](http://tla2012.loria.fr/contributed/newcombe-slides.pdf) описано как model checker смог найти пример для readOnly аномалии длины 9, а авторы приводят приводят пример из 10 шагов.

Понятно, что такой способ линеен от кол-ва состояний (кол-во состояний = exp(кол-во шагов)). Для бесконечных спек мы должны сделать спеку конечной. Этот способ подойдет, когда мы проверяем, что выполняются св-ва алгортима.

Большинство багов распределенных систем требуют большой длины трейса. При запуске TLC в обычном режиме потребуется сначала исследовать все короткие трейсы перед тестированием более длинных.

Но что, если мы хотим какой-то необычное поведение, которое требует большого количества шагов?

Для поиска "интересных" поведений можно воспольщоваться не систематическим исследованием графа конфигураций, а Simulation mode. В этом методе чекер случайно выбирает траекторию и исследует ее на выполнение св-вам. Этот метод не поможет проверить, что наша спека удовлетворяет всем св-вам, которые мы описали, так как он не проводит полную проверку графа состояний.

Например, этот способ можно использовать чтобы найти ReadOnlyAnomaly в спеке SI.

## Почему мы можем рассматривать небольшие модели
Model checker явно исследует граф состояний - для проверки инвариантов ему нужно обойти каждое достижимое состояние, а для проверки произвольных темпоральных свойств – явно разложить весь граф в памяти и найти в нем сильно связные компоненты, а размер графа будет экспоненциально зависеть от значений упомянутых выше параметров. Из-за этого мы хотим уменьшить кол-во состояний системы и проверить наши св-ва.

Поэтому разумно с помощью TLC проверять только небольшие модели в которых число участников/действий небольшое число. Например: proposal-ов в Basic Paxos, транзакций в Percolator, аппендов в Kafka измеряется единицами (3-5), в то время как в реалной системе их на многие порядки больше, так как число состояний = exp от параметров системы. Так как если у нас a состояний и b компонент, то получается, что кол-во вершин в графе конфигураций = b^a

Тем не менее, model checking даже для таких небольших моделей может убеждать в корректности. Так как он полностью исследует все возможные выполнения системы.

Примеры:
* Контрпример для Basic Paxos: аксепта одного значения на большинстве узлов недостаточно для понятия выбора - достаточно 4 proposal-ов
* Баги в lf алгоритмах чаще всего можно промоделировать на очень небольшом числе потоков, независимо от сложности самого бага, пример с длинным багом в lf аллокаторе
* RO аномалия для SI достигается на 3 транзакциях и 2 ключах

В статье "https://www.usenix.org/system/files/conference/osdi14/osdi14-paper-yuan.pdf" аторы заметили: "Almost all (98%) of the failures are guaranteed to manifest on no more than 3 nodes. 84% will manifest on no more than 2 nodes…. It is not necessary to have a large cluster to test for and reproduce failures."

Заметим, что даже полная проверка на небольшой модели не может служить служить доказательством корректности в общем случае, но природа конкурентных багов такова, что они часто не зависят от кол-ва участников (если их больше 1), а зависят от порядка действий.

## SW и WF
liveness св-ва о прогрессе нашей системы. Они говорят о том, что алгоритм движется вперед, а не стоит на месте. Когда мы пишем liveness св-ва мы хотим, чтобы к нашей системе планировщик/OS относилась честно и мы будем прогрессировать, если сможем. В TLA+ мы должны явно указать какие переходы надо делать, когда они будут верны. Мы не убираем недетерминированный выбор. Алгорит или OS все равно могут делать недетерминированные шаги, но мы хотим подсказать чекеру, какие шаги ему надо делать "честно". Но для большинства распределенных систем liveness св-ва не проверяются.

В TLA есть 2 оператора для обеспечения честности шагов алгоритма:
* WF - Если переход в экшен A есть из каждого состояния цикла, то мы точно перейдем в A
* SF - Если экшен A выполнен бесконечно-часто, то он будет выполнено. То есть если мы попали в цикл в нашем графе конфигураций и есть состояние в этом цикле из которого можно перейти в A, то мы выполним переход когда-то

! SF => WF !

Мы как будто разрешаем спецификации видеть будущее и принимать решения на выбор траектории.

Что на самом деле дает нам честность? Мы хотим ограничить траектории, которые не совершают какой-то прогресс. Например, какие-нибудь бесполезные поведения, которые могут происходить, но они не будут удовлетворять нашим требованием от системы. Мы хотим проверять инварианты относительно какого-то полезного поведения.

Пример: В спеки Kafka есть честность у некоторых действий.

Например:

    Spec == Init /\ [][Next]_vars
                 /\ SF_vars(LeaderIncHighWatermark)
                 /\ SF_vars(LeaderExpandIsr)
                 /\ SF_vars(LeaderWrite)
                 /\ WF_vars(BecomeFollowerTruncateToHighWatermark)
                 /\ WF_vars(BecomeLeader)

у нас может быть траектория, в которой нет лидера и, следовательно, чекер в такой ситуации не будет брать важные и системы не будет совершать "прогресс"  (принимать записи, или увеличивать метку записей, которые точно должны быть у всех реплик). Авторы хотят избежать таких "бесполезных" траекторий, так как св-ва на них проверять бессмысленно. Поэтому они дают экшену `BecomeLeader` приоритет.

## Symetry
