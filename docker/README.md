# Local Docker/CSI verification

Besides Azure Pipelines tests performed on every commit pushed upstream there is a possibility to run all tests defined for Azure Pipelines locally.
For this purpose a special CSI container was created, which contains all required dependencies and provides easy way of all running tests in current repository.

## Running tests

### Docker Compose

If you have Docker Compose installed it's the easiest way of executing tests.
Every time you need to perform tests just run in `docker/` directory:

```
docker-compose up
```

### Docker/Podman

To build and run tests using Docker or Podman run following commands in `docker/` directory:

```
docker build -t ibex-tests .
docker run --rm -v $PWD/../:/home/ibex/repo -it ibex-tests
```

(if you're using Podman it's assumed that it's aliased to `docker` command)

## Adding tests

Dockerfile is tightly connected with `azure-pipelines.yml` file, which can be found in root directory.
All changes in `Dockerfile` or `entrypoint.sh` should also be added in `azure-pipelines.yml` and vice versa.

All steps that are static dependencies in `azure-pipelines.yml` should be imported to `Dockerfile`, whereas all tests performed on currently tested repository should go to `entrypoint.sh`.

For CSI image dependencies should be build in `/home/ibex/build`.
The code resides in mounted volume in `/home/ibex/repo`.
