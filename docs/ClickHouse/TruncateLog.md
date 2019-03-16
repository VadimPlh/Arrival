### Очистка лога от старых записей

В зукипере для есть нода /log, где хранится лог всех действий, которые приходят на реплики [тут](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L354)
Так как лог разрастается в зукипер кидает ошибку, так как у него слишком много нод образовалось.
Чтобы этого не было были принято решение чистить лог до самой минимальной по номеру записи.
Но тут есть проблема,что если реплика была отключена и долгое время не включалась, то лог будет так же расти

У каждой реплики [лог поинтер](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L518) указывает на текущую запись, которую реплика выполняет
Так же у каждой реплики есть состояния:
* [Active](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeRestartingThread.cpp#L276) эфимерная нода, которая показывает досткп реплики до Zookeeper-а
* [is_lost](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L522) нода, которая говорит есть ли сейчас в зукипере записи, на которые указывает log_pointer

Что же происходит:
* У каждой реплики есть [ReplicatedMergeTreeCleanupThread](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeCleanupThread.cpp#L20). Во время создания таблицы он [запускается](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L224)
* Тред [смотрит](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeCleanupThread.cpp#L69) на лог в зукипере забирает к себе все сушествующие записи
* Выбирается записи, которые должны удалиться из активных 
