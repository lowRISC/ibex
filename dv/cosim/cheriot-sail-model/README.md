# CHERIoT Specification and Sail model

This repository contains the specification for the [CHERIoT](https://cheriot.org) ISA.
It consists of a document written in [latex](/archdoc) which includes excerpts of the [reference model](/src) written in [Sail](http://github.com/rems-project/sail).
The [current draft architecture document](https://cheriot.org/cheriot-sail/cheriot-architecture.pdf) built from this repository contains a full description of the ISA and its intended use by [CHERIoT RTOS](https://github.com/CHERIoT-Platform/cheriot-rtos/).
The Sail code is used to build an instruction set simulator which is included in the [CHERIoT RTOS dev container](https://github.com/CHERIoT-Platform/cheriot-rtos/blob/main/docs/GettingStarted.md).
It can also be used to prove [properties](properties) of the ISA using Sail's SMT support.

The architecture is based on the [CHERI specification](https://github.com/CTSRD-CHERI/cheri-specification).
The code is derived from [sail-cheri-riscv](http://github.com/CTSRD-CHERI/sail-cheri-riscv) and uses [sail-riscv](http://github.com/rems-project/sail-riscv) as a submodule.

# Building

The easiest way to use the emulator is to use the dev container for the CHERIoT RTOS as described in the [getting started guide](https://github.com/CHERIoT-Platform/cheriot-rtos/blob/main/docs/GettingStarted.md).

Alternatively, if you wish to build from source you must first install dependencies, including Sail. For example, on Ubuntu 20.04 we have tested:

```
sudo apt update
sudo apt install opam z3 libgmp-dev
opam init
opam install sail
```

If you haven't already, set up your environment for `opam`, otherwise you will get `make: sail: No such file or directory` as an error during compilation:

```
eval $(opam env)
```

Then clone the repo:

```
git clone --recurse-submodules https://github.com/CHERIoT-Platform/cheriot-sail
cd cheriot-sail
```

Finally build the C emulator:

```
make csim
```

This will produce an executable in `c_emulator/cheriot_sim` that can be used to run ELF files produced by the CHERIoT compiler.

To build the documentation you must have `biber`, `latexmk` and `pdflatex` and have setup your `opam` environment as above. Then follow the following commands:

```sh
pushd archdoc
make
popd
```

This will create a file located at `archdoc/cheriot-architecture.pdf`.

## Contributing

This project welcomes contributions and suggestions.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.
