# Unit tests

```sh
make  VLT_TOP_MODULE=tb_isolde_addr_shim veri-clean verilate veri-run-u-test
```
```sh
make  VLT_TOP_MODULE=tb_isolde_mux_tcdm veri-clean verilate veri-run-u-test
```

```sh
make  VLT_TOP_MODULE=tb_isolde_template veri-clean verilate veri-run-u-test
make  VLT_TOP_MODULE=tb_isolde_log_interconnect veri-clean verilate veri-run-u-test
make  VLT_TOP_MODULE=tb_isolde_hci_interconnect veri-clean verilate veri-run-u-test
```
