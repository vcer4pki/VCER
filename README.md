# V'CER
### Validating Certificates Efficiently in Resource-Constrained Networks

Uses a collection of Sparse Merkle Trees for efficient certificate validation and updates. 
Further, it defines operations to allow for distributed repair among nodes to repair validation information of nodes 
that missed updates without the need to contact the CA.

- **ca.py** contains logic for constructing a Validation Forst as well as constructing updates and caches
- **smt_util.py** contains logic for handling PoIs and update caches for local users

#### Evaluation Classes:
- **ops_big_tests.py** has methods for extensive validation tests of individual operations
- **ops_runtime.py** prints runtimes of individual operations regarding processing overhead
- **sim.py** contains simulation that models contrained networks