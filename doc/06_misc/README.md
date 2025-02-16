# ISOLDE

```sh
. ./env.sh
```
it will activate the environment for generating the report(s)

## Export current environment
```sh
pip3 list --format=freeze | grep -v "@" > python-requirements.txt
```
## Update the current environment
```sh
pip3 install -U -r python-requirements.txt
```