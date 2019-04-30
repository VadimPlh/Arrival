## Модель данных в ZK
### Общая модель
* /metadata - структура таблицы
* /columns - структура таблицы
* /log - лог событий
* /blocks - список последних N блоков с чексуммами для проверки дедупликации
* /block_numbers - нода с увеличивающимся id для блоков, которые втсавляем
* /nonincrement_block_numbers
* /leader_election - нода для выборов лидера
* /temp -
* /replicas - список реплик для текущей таблицы
* /mutations - отображение записей о мутациях

### /log
Содержит информацию о событях(вставки, мерджи и т.п.). Последовательные записи.
Ноды имеют вид /log-xxxxx;
В информации содержится:
The replicated tables have a common log (/log/log-...).
  * - normal data insertion (GET),
  * - merge (MERGE),
  * - delete the partition (DROP).

### /replicas/<name_replica>/
* /host - хост создателя реплики
* /log_pointer - указатель на запись в логе, включително которо
* /queue - локальнвая очередь здач каждц реплики, сюда они попадают из общего лога
* /parts -
* /flags -
* /is_lost - флаг, который показывает, удалены ли нужные запими из лога для этой реплики
* /columns

### /leader_election


### /quorum
