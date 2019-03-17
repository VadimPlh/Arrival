## Репликация в ClickHouse
### Краткое изложение
У нас в зукипере хранится лог. В него летят информация о вставках, назначенных мерджах
У каждой реплики есть log_pointer который указывает на какую-то запись в логе
Реплики берут заливают к себе в очередь все записи из лога начиная с их log_pointer
и передвигают его.

### Вставка куска
* На реплику прилетает вставка
* Запись происходит вот [тут](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeBlockOutputStream.cpp#L107).
* Если вставка с кворумом, то происходит проверка некоторых условий.(об этом в другом месте)
* Происходит разделение блока по партициям для вставки. (Мы считаем, что раболтаем в пределах одной, так как для спек это несуществено)
* Происходит [запись временного куска](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeBlockOutputStream.cpp#L133) на ФС и прочая магия
* Для дедупликации происходит  [вычесление](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeBlockOutputStream.cpp#L137) чексуммы от куска
* Следующий шаг - это [commitPart](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeBlockOutputStream.cpp#L203)
* Первым делом мы должны [выделить](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeBlockOutputStream.cpp#L215) для куска id, который будет уникальным для партиции. 

### Выполнение лога
