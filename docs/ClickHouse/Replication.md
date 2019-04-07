## Репликация в ClickHouse
### Важный момент
Мы не моделируем отпраку сообщений в нашей системе. В КХ реплики общаются между собой только для скачивания недостающих кусков.
Все остальное взаимодействие происходит через shared memory, которую выполняет зукипер.

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
* Проверка для [дедупликации](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L3688)
* [Пишем](https://github.com/yandex/ClickHouse/blob/a0d8743c4c1249f1e2394c6eb47bbbfcc83c502d/dbms/src/Storages/MergeTree/ReplicatedMergeTreeBlockOutputStream.cpp#L226) инфу о блоке
* [Создаем](https://github.com/yandex/ClickHouse/blob/617a0a8938533f86902d431ae8b923b654932fc6/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L4911) транзакцию со вской инфой для блока
* [Добавляем](https://github.com/yandex/ClickHouse/blob/a0d8743c4c1249f1e2394c6eb47bbbfcc83c502d/dbms/src/Storages/MergeTree/ReplicatedMergeTreeBlockOutputStream.cpp#L252) запрос на добавление в лог
* Осуществяем транзацию [тут](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeBlockOutputStream.cpp#L304)
* Если проблемы, то откатываем


### Выполнение лога
* При создании таблицы создается таска, которая [выполняет](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L237) очередь задач
* Первым делом мы [загружаем](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2019) в свое очередь задачи из зукипера
* [берем](https://github.com/yandex/ClickHouse/blob/1446c50884ca3daaeec7af903a2a7b308d85a0ad/dbms/src/Storages/MergeTree/ReplicatedMergeTreeQueue.cpp#L391) текущий log_pointer
* Загружаем к себе текущий лог и [удаляем](https://github.com/yandex/ClickHouse/blob/1446c50884ca3daaeec7af903a2a7b308d85a0ad/dbms/src/Storages/MergeTree/ReplicatedMergeTreeQueue.cpp#L418) из него все записи меньше нашего указатель
* [Перетаскиваем](https://github.com/yandex/ClickHouse/blob/1446c50884ca3daaeec7af903a2a7b308d85a0ad/dbms/src/Storages/MergeTree/ReplicatedMergeTreeQueue.cpp#L469) данные из лога в свою очередь в зукипере
* [Двигаем](https://github.com/yandex/ClickHouse/blob/1446c50884ca3daaeec7af903a2a7b308d85a0ad/dbms/src/Storages/MergeTree/ReplicatedMergeTreeQueue.cpp#L484) log_pointer
* Чуть магии с обновлением заданий в RAM
* [Будим](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2066) queueTask
* [Выбираем](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2080) задания для исполнения
* Задание будет выполнено, если [не происходит слияний](https://github.com/yandex/ClickHouse/blob/1446c50884ca3daaeec7af903a2a7b308d85a0ad/dbms/src/Storages/MergeTree/ReplicatedMergeTreeQueue.cpp#L1083) с ним, например. (Кажется, что можно не возиться с очередью в спеке, и считать, что мы просто выполняем записи из лога сразу, без буфера этого)
* [Пытаемся](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2098) выполнить запись
* [Смотрим](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L851) на тип задачи и на то, надо ли скачивать кусок или нет, и выполняем требуемое
* Делаем после этого [executeFetch](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L1253)
* [Ищем](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L1255) реплику  нужным куском
* Пытаемся [забарать](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L1392) его у нее. (Там же с кворумом делаем обновление)
* Если куска нигде нет, то делаем [enqueuePartForCheck](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L1426)


Что-то с PartCheker-ом
