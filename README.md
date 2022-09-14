# MongoDBCC
Formal specification and verification of causal consistency protocol of MongoDB in TLA+.

Each sub-protocol is specified in a .tla file named by BasicCC, DurableCC or RecoverableCC.
- BasicCC describes the causal protocol under a failure free scenario;
- DurableCC describes the causal protocol under the scenario for node crash;
- RecoverableCC describes the causal protocol under the scenario that node crash, failover and rollback may happen. It is the causal consistency protocl that MongoDB uses in practice
