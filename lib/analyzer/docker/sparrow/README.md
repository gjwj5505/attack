# Sparrow Docker wrapper

Sparrow analyzes preprocessed C files (`.i`).

Build:

```bash
docker build -t ropas-sparrow lib/analyzer/docker/sparrow
```

Run on a preprocessed file:

```bash
lib/analyzer/docker/sparrow/run-sparrow.sh path/to/file.i
```

For a `.c` file, preprocess first:

```bash
cpp -P examples/simple.c > /tmp/simple.i
lib/analyzer/docker/sparrow/run-sparrow.sh /tmp/simple.i
```
