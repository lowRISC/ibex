MINICONDA_ENV=ibex
. ~/miniconda3/etc/profile.d/conda.sh
conda create --name $MINICONDA_ENV python=3.10
conda activate $MINICONDA_ENV 
pip3 install -U -r python-requirements.txt
make -f Makefile.tools
. ./eth.sh 