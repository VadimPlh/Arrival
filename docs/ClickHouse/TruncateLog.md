## Spec
Что мы хотим моделировать:
* log - лог в зукипере.
* replicaState - состояние реплики
* deletedPrefix - префикс, который мы удалили из лога. Для простоты поддерживаем просто границу удаленных записей в логе

Что такое состояние реплики:
* is_active - нода в зукипере, говорит, что связь с зукипером не прервана
* is_lost - нода в зукипере, нужные ноды в логе удалены
* log_pointer - указатель на запись в логе, до которой все выполнили.

![image](https://github.com/VadimPE/Arrival/blob/master/docs/ClickHouse/TruncateLog.png)

Основные экшены в спеке:
* Событие, что реплика стала неакивной (Для этого просто убираем флаг активности у реплики. Моделируем эфимерную ноду)
* Событие, что реплика снова стала активной (Восстановление связи с зукипером и появление эфимерной ноды)
* Выполнение лога в зукипере (Существует активная реплика, у которой лог поинтер отстает от головы лога)
* Вставка новых записей в лог (Вставляем запись в лог. Активная реплика создала новую ноду в зукипере)
* Очитска лога (Выбираем максимум из существующего префикса и манимального лог поинтера активных реплик и меняем состояние реплки, чьи log_pointer-ы меньше)
* Клонирование состояния у активной реплики (выбираем активную реплику и переносим состояние ее к себе)

Чем пользуемся:
* Для того, чтобы проверить, что существует поведение, когда одна из реплик становится is_lost, запускаем TLC с условием HasNotLostReplica и находим интересующее нас поведение
* Для проверки св-ва `IsLogCleared` мы ограничиваем велечину лога константой.

Время работы:
* Replicas = 3, LenLog = 7 - 13sec
* Replicas = 3, LenLog = 20 - 1min 58sec
* Replicas = 5, LenLog = 7 - бесконечность

## Очистка лога от старых записей
В зукипере для есть нода /log, где хранится лог всех действий, которые приходят на реплики [тут](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L354)
Так как лог разрастается в зукипер кидает ошибку, так как у него слишком много нод образовалось.

Чтобы этого не было были принято решение чистить лог до самой минимальной по номеру записи.
Но тут есть проблема,что если реплика была отключена и долгое время не включалась, то лог будет так же расти

У каждой реплики [лог поинтер](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L518) указывает на текущую запись, которую реплика выполняет.

Так же у каждой реплики есть состояния:
* [Active](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeRestartingThread.cpp#L276) эфимерная нода, которая показывает досткп реплики до Zookeeper-а
* [is_lost](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L522) нода, которая говорит есть ли сейчас в зукипере записи, на которые указывает log_pointer

Что же происходит:
* У каждой таблицы есть [ReplicatedMergeTreeCleanupThread](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeCleanupThread.cpp#L20). Во время создания таблицы он [запускается](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L224),
 удаление старых записей делает [лидер](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeCleanupThread.cpp#L62), но не страшно, если лидер поменяется и сразу две реплики будут пытаться чистить лог.
* Тред [смотрит](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeCleanupThread.cpp#L69) на лог в зукипере забирает к себе все сушествующие записи
* Выбирается записи, которые должны удалиться (выбираем минимум из поинтеро активных реплик и восстанавливающихся, так же есть настройка, которая гооворит о том сколько записей мы точно оставим в логе)
* Мы [помечаем](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeCleanupThread.cpp#L232) реплики у которых удалим лог, как is_lost
* В транзакции смторим, что реплики не стали снова active и помечаем их умершими, так же надо смотреть, что мы не пометим все реплики lost, так как тогда они не смогут восстановиться.
* Дальше мы должны удалить старые записи из лога. В этот момент важно видеть, что у нас [не появилось новой реплики](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeCleanupThread.cpp#L222)

### Восстановление реплики
* Во время создания таблицы создается  [ReplicatedMergeTreeRestartingThread](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L224)
* Дальше при создании реплики, если она не первая, то ей ставится [is_lost](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L512) для восстановления
* Если реплика не стартовала или была потеряна связь с зукипером, то он делает [tryStartUp()](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeRestartingThread.cpp#L164)
* Первым делом мы помечаем реплику как [is_active](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeRestartingThread.cpp#L276) (Это важно, так как после этого записи в логе для нее не будут удаляться).
* Следующим шагом по пробуем [клонировать](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/MergeTree/ReplicatedMergeTreeRestartingThread.cpp#L173) реплику, если это [необходимо](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L1958).
* [Ищем](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L1977) реплику для восстановления
* Делаем [CloneReplica](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L1863)
* [Получаем log_pointer](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L1892) и в транзакции установливаем у нас  log_pointer и проверяем, что реплика, с которой мы восстанавливаемся, [не стала is_lost](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L1903).
* Скачиваем себе все отсальные данные.
* После убираем пометку, что мы [is_lost](https://github.com/yandex/ClickHouse/blob/93356b519039aac5b9b2111ecb75344cc9ae62ee/dbms/src/Storages/StorageReplicatedMergeTree.cpp#L2006).

Важно, что в момент восстановления мы были и is_lost и is_active. Таким образом мы поддерживаем инвариант, что лог для нас не удалится и мы сможем его исполнять,
но другие реплики не смогут клонироваться с нас, чтобы не застать промежуточное состояние наше в момент скачивания данных.
