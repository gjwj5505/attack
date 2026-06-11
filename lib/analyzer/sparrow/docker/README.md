# Sparrow Docker wrapper

Sparrow analyzes preprocessed C files (`.i`).

Build:

```bash
docker build -f lib/analyzer/sparrow/docker/Dockerfile -t attack-sparrow lib/analyzer/sparrow
```

Run on a preprocessed file:

```bash
lib/analyzer/sparrow/docker/run-sparrow.sh path/to/file.i
```

For a `.c` file, preprocess first:

```bash
cpp -P examples/simple.c > /tmp/simple.i
lib/analyzer/sparrow/docker/run-sparrow.sh /tmp/simple.i
```
