## RQ1 Experimental Results

The `RQ1_result` directory contains the core experimental results for Research Question 1 (RQ1), which evaluates the effectiveness of the migration framework. These experiments were conducted on **160** migratable C programs whose paths are recorded in the `data/dataset_path/supported_benchmark.txt`.

- `migration_success`: 
    This folder contains **117** files that were successfully migrated using the framework, possibly with minimal manual fixes (<= 4 LoC).

- `migration_failure`: 
    This folder contains **43** files where migration failed.

- `success_without_minimal_fix`:
    This folder contains 90 files.