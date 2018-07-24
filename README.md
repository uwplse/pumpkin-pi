## Dependencies

The only dependency to use the plugin is Coq 8.8.

To run the case study code, you also need the following:
* An opam switch with Coq 8.7.2
* The univalent parametricity framework: https://github.com/CoqHott/univalent_parametricity

This is because their framework is not on Coq 8.8, and we evaluate in comparison to them. We will eventually
package all of this into a VM for reproducibility, but for now, we include the directions manually.

## Building

### Plugin

```
coq_makefile -f _CoqProject -o Makefile
make && make install
```

### Case Study Dependencies

```
opam switch <switch-with-coq-8.7.2>
eval `opam config env`
cd <path-to-univalent-parametricity>
coq_makefile -f _CoqProject -o Makefile
make && make install
```
