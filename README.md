# CleanQ Proofs in Isabelle/HOL

The CleanQ proofs in the Isabelle/HOL theorem prover.


## License

See the LICENSE file. For the dependencies, see their licenses. 


## Authors

 * Roni Haecki
 * Reto Achermann
 * David Cock


## Dependencies

 * [Isabelle/HOL 2019](https://isabelle.in.tum.de/website-Isabelle2019/index.html)
 * TexLive 
 * Make
 * AutoCorres / Simpl / Complex: `make deps`


## Compiling and Running

We provide make targets for building the proof documetation. For this, make sure
you obtained the dependencies either manually, or using `make deps`

Then you can build the proofs and the documentation using

```
make
```

This should build a PDF `build/cleanq-proofs.pdf`.

