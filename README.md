# FOL Software Archaeology

This fork updates the code to run on [Allegro Common Lisp](https://franz.com/downloads/clp/survey) and [SBCL](http://www.sbcl.org/).

In addition, it strives to reproduce the results of the [Prolegomena](tst/prolegomena).

## How to run

- `mkdir -p o` from project directory
- set `%HOME-DIR%` variable to this project's absolute root directory in [make/host.lsp](make/host.lsp#L86) 
- open `alisp` or `sbcl` from [make](make) directory
- `(load "install.lsp")`
- `(MAKE-GETFOL)`
- `(SYSBOOT)`
- `fetch ../tst/TEST;`
- `fetch ../tst/LONGTEST;`
- `fetch ../tst/prolegomena/RUN;`

## Creating an executable

- `sbcl --script boot.lsp` from [make](make) directory will create a `GETFOL` executable
