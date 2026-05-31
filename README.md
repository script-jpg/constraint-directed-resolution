# constraint-directed-resolution
## Layout
The `ConstraintDirectedResolution` folder contains three main files: `main.lean`, `checker.lean`, and `program.lean`
- `main.lean` has the definitions and proof results
- `checker.lean` has the custom tactic
- `program.lean` defines the sequential program
- `examples` folder contains different executable examples
## Build Instructions
To build do the following:
1. Ensure you have elan:
`curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh`
2. Clone the repo and cd into the root
3. Do `lake exe cache get`
4. Do `lake build`
## Acknowledgements
We acknowledge proof support from Aristotle (Harmonic)