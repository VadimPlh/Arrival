## Quorum Insert and Selec
Алгоритм для вставки и чтения с кворумом

Как трекается нода с кворумом:
* Во время выполнения лога, мы смотрим под кворумом ли эта запись и если да, то [обновляем](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2781)
* Пытаемся [получить](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2572) ноду со статусом кворума, если нет, то кворум закончился
* [Добавляем](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2583) себя к репликам в кворуме
* [Если кворум набрался](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2585), то удаляем ноду со статусом и [обновляем](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2606) записанные с кворумом куски
* Иначе просто [увеличиваем](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2629) число реплик в кворуме

### Select
----------
* На реплику [приходит](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2879) SELECT
* Смотри, включена ли [sequential_consistency](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2894)
* Мы для каждой партиции выбираем максимальный блок, который в нее вставлен
* Делаем это для всех патрицый [просто](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2900)
* для текущего кворума максимальный блок [уменьшаем](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2917) на единицу, чтобы не отдать кусок, который еще не собрал нужное кол-во подтверждений
* Дальше из всех блоков с кворумом [выбираем](https://github.com/yandex/ClickHouse/blob/6b690aaf723e26fba65d83e06b6a2d029e028545/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2935) максимальный для каждой партиции

### Insert
----------
вставка как обычная, но с условием [тут](https://github.com/yandex/ClickHouse/blob/a0d8743c4c1249f1e2394c6eb47bbbfcc83c502d/dbms/src/Storages/MergeTree/ReplicatedMergeTreeBlockOutputStream.cpp#L265)
смторим, что реплика не рестартовала, и делаем запись для кворума
