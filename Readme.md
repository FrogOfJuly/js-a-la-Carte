# Modular take on Javascript formalization in Rocq

Inspiration is taken from [here](https://github.com/uds-psl/coq-a-la-carte-cpp20/tree/master).

## Build

[Install opam](https://opam.ocaml.org/doc/Install.html)

```bash
opam switch create modular_js --packages="ocaml-variants.4.14.0+options,ocaml-option-flambda"
eval $(opam env)
opam pin add coq 9.0.0
opam pin add rocq-equations 1.3.1+9.0
coq_makefile -f _CoqProject -o Makefile && make
```

