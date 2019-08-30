# FOL Software Archaeology

This fork updates the code to run on [Allegro Common Lisp](https://franz.com/downloads/clp/survey).

In addition, it strives to reproduce the results of the [Prolegomena](tst/prolegomena).

## How to run

- `mkdir -p o` from project directory
- open `alisp` from [make](make) directory
- `(load "install.lsp")`
- `(MAKE-GETFOL)`
- `(SYSBOOT)`
- `fetch ../tst/TEST`
- `fetch ../tst/LONGTEST`
- `fetch ../tst/prolegomena/RUN`
