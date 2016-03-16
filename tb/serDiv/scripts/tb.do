###############################################################################
## Title        :  testbench starter script (with GUI)
## Project      :  Approximate Cholesky Solver
## Purpose      :  compiles all sources and generates the testvectors
## Author       :  Michael Schaffner (schaffner@iis.ee.ethz.ch)
###############################################################################
## File ID      :  $Id: tb.do 756 2014-06-20 12:41:06Z michscha $
## SVN Rev.     :  $Revision: 756 $
## Date:        :  $Date: 2014-06-20 14:41:06 +0200 (Fri, 20 Jun 2014) $
## Modified by  :  $Author: michscha $
###############################################################################
## Major Changes:
## Date        |  Author     |  Description
## 2014/01/18  |  schaffner  |  created
###############################################################################
## Description:
##
## 
###############################################################################
## Copyright (c) 2014 Disney Research Zurich, Integrated Systems Lab ETH Zurich
###############################################################################

#vsim -sva -assertdebug -t ps tb
vsim -voptargs="+acc" -t ps tb

#turn off disturbing warnings...
#set NumericStdNoWarnings  1

do wave.do
run -all
