
if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) )))
  from HWModel.model import *
  from HWModel.sc_model import *
  import HWModel.hw_z3 as hw
else:
  from HWModel.model import *
  from HWModel.sc_model import *
  import HWModel.hw_z3 as hw

from tso_plus import *
from pso_plus import *

__modelList = {
	'SC': SCModel()
	,'TSO+':TSOPlusModel()
  ,'PSO+':PSOPlusModel()
	}

def models():
	return __modelList.keys()

def getModel(model = 'SC'):
	if model in __modelList:
		return __modelList[model]
	else:
		return None

