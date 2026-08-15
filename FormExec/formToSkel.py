import sys
import os
import json
import shutil
import subprocess
#from decimal import Decimal, ROUND_DOWN


global cptSection
global cptForm
global cptDef
cptForm = 0
cptDef = 0
cptSection = 1

def dataOrLink(value):
	datas = value.strip().split(",")
	#If a single value, then it is a normal value
	if len(datas)==1:
		return False, value
	#Else it is a link
	else:
		return True, datas[1]

# Use to print the timer using different kinds of measures (milliseconds, seconds, etc.)
def choiceOfTime(timer, many, maxDecimalArg):
	try:
		if timer=='milliseconds':
			#return (str(float(many)*1000.)+" ms")
			return ("{:."+maxDecimalArg+"f}ms").format(float(many) / 1e+6)
		elif timer=='microseconds':
			#return (str(float(many)/1000000.)+" s")
			return (("{:."+maxDecimalArg+"f}").format(float(many) / 1000.)+"\\textmu s")
		elif timer=='nanoseconds':
			#return (str(float(many)/1000000000.)+" ns")
			return ("{:."+maxDecimalArg+"f}ns").format(float(many) )
		elif timer=='seconds':
			return ("{:."+maxDecimalArg+"f}s").format(float(many) / 1e+9)
		elif timer=='minutes':
			m,s = divmod(float(many)/1e+9,60.)
			return "{:02.0f} mns {:02.0f} s".format(m,s)
		elif timer=='hours':
			m,s = divmod(float(many)/1e+9,60.)
			h,m = divmod(m,60.)
			return "{:02.0f}h {:02.0f}mns {:02.0f}s".format(h,m,s)
		else:
			return ("{:."+maxDecimalArg+"f}ns").format(float(many))
			#return (many+" s")
	except:
		return ("\\todo[inline,color=red!40]{FormSkel-error: choiceOfTime fail to converting time "+str(many)+"using "+timer+" measure}")


######### What to do when reaching \end{document} #########
#### Write the computation in a end.py file !!!!
def formulaToSkelEnd(server,serverDir,ServerAccess,localLib):
	if not os.path.exists("formSkel"):
		try:
			os.mkdir("formSkel")		
		except (OSError, IOError) as e:
			pass

	global cptSection
	global cptForm
	global cptDef
	try:
		namefileEnd = "./formSkel/end.py"
		# Write end.py only if it does not exit yet
		# NOT Write it all the time (????)
		#if not os.path.exists(namefileEnd):
		fileEnd = open(namefileEnd, "w")

		## The code of the end.py 
		code = """
import os

# Write the number of formulas of the last section
fileF = open("./formSkel/nbFormules.section"+str("""+str(cptSection)+""")+".formSkel.in", "w")
fileF.write(str("""+str(cptForm)+"""))
fileF.close()

# Write the number of definition of the last section
fileF = open("./formSkel/nbDefs.section"+str("""+str(cptSection)+""")+".formSkel.in", "w")
fileF.write(str("""+str(cptDef)+"""))
fileF.close()

# Write the number of sections in a file
fileS = open("./formSkel/nbSections.formSkel.in", "w")
fileS.write(str("""+str(cptSection)+"""))
fileS.close()

for i in range(1,"""+str(cptSection)+"""+1):
	name = "./formSkel/environment.section"+str(i)+".formSkel.in"
	try:
		os.rename(name+".tmp", name)
	except (OSError, IOError) as e:
		pass

try:
	os.remove("./formSkel/assocLabelNumber")
except (OSError, IOError) as e:
	pass
	
fileServ = open("./formSkel/infoServer.formSkel.in", "w")
fileServ.write("""+"\'"+server+"\'+\'\\n\')\nfileServ.write("+"\'"+serverDir+"\\n\')\nfileServ.write("+"\'"+ServerAccess+"\\n\')\nfileServ.write("+"\'"+localLib+"\\n\')\nfileServ.close()\n"

		fileEnd.write(code)
		fileEnd.close()
	except (OSError, IOError) as e:
		pass

######### Changing of section #########
def nextSectionFormSkel():
	global cptSection
	global cptForm
	global cptDef

	# Write the number of formulas of the last section
	fileF = open("./formSkel/nbFormules.section"+str(cptSection)+".formSkel.in", "w")
	fileF.write(str(cptForm))
	fileF.close()

	# Write the number of definitions of the last section
	fileF = open("./formSkel/nbDefs.section"+str(cptSection)+".formSkel.in", "w")
	fileF.write(str(cptDef))
	fileF.close()
		
	# Increasing the number of section (in the file)
	cptSection = cptSection + 1
	# Reset to 0 the number of formulas
	cptForm = 0
	cptDef = 0

def currentSectionFormSkel():
	global cptSection
	print(cptSection)


#Del the surrounding dollars and what is behind each percent (comments)
def delDollarsAndPercent(text):
	withoutDollars=(text.strip()).strip("$")
	comment = False
	newText=[]
	for i, c in enumerate(withoutDollars):
		if ((i>0) and (c=='%') and (withoutDollars[i-1]!='\\')):
			comment=True
		if ((i>0) and (c=='\n')):
			comment=False
		if not(comment):
			newText.append(c)
	return (''.join(newText)).strip()

#TODO: much more try needed !
######### Adding a formula in the file of the tool #########
def formulaToSkel(formula):

	# Delete the surrounding dollars and comments
	formula = delDollarsAndPercent(formula)

	# Creating the directory to put the file if needed and the end.py
	try:
		os.mkdir("formSkel")
	except (OSError, IOError) as e:
		pass

	global cptSection
	global cptForm
	global cptDef

	indiceDef  = formula.find("\\eqdef")
	isDef = (indiceDef != -1)

	# Find the defined name
	if isDef:
		nameDef = (formula[:indiceDef].strip()).strip("\\")

	if isDef:
		cptDef = cptDef + 1
	else:
		cptForm = cptForm + 1

	# namefileIN, the input of the execution tool
	if isDef:
		namefileIN = "./formSkel/section"+str(cptSection)+".definition."+str(nameDef)+".formSkel.in"
	else:
		namefileIN = "./formSkel/section"+str(cptSection)+".formula"+str(cptForm)+".formSkel.in"

	# namefileOUT, the output of the execution tool
	if isDef:
		namefileOUT = "./formSkel/section"+str(cptSection)+".definition."+str(nameDef)+".formSkel.out"
	else:
		namefileOUT = "./formSkel/section"+str(cptSection)+".formula"+str(cptForm)+".formSkel.out"

	#Some information for the formulaToSkel routine (executed next) ==> adding if it is a formula or a definition
	namefileDEF = "./formSkel/defOrNot"
	fileDEF = open(namefileDEF, "w")
	fileDEF.write(str(isDef))
	if isDef:
		fileDEF.write(str(nameDef))
	fileDEF.close()

	try:
		# If the file still exists 
		# then we must first verify if it has changed or nor before adding the formula
		# else adding the formula
		# TODO: verifying if the user change the language and so run again !
		if os.path.exists(namefileIN):
			fileFormToSkelIN = open(namefileIN, "r")
			old = fileFormToSkelIN.read()
			fileFormToSkelIN.close()
			# the formula has changed
			if old!=formula:
				# So write the formula in the file
				fileFormToSkelIN = open(namefileIN, "w")
				fileFormToSkelIN.write(formula)
				fileFormToSkelIN.close()
				# Delete the previous output
				try:
					os.remove(namefileOUT)
				except (OSError, IOError) as e:
					pass
				# Explain that to the user or nothing in case of a definition
				if isDef:
					print("")
				else:
					print("\\text{\\todo[inline,color=red!40]{")
					print("You change your formula, a new result will be generated by the FormSkel tool, so you need to run: (1) FormSkel and its generated Makefile; (2) pdflatex so to get the result of your new Formula "+str(cptForm)+" of Section "+str(cptSection))
					print("}}")
			else:
				# If the formula has not changed then 
				# If the output exists then
				# it is ok, the result will be show by the command "formulaToSkelValue"
				# otherwise write an error message to LaTeX
				if os.path.exists(namefileOUT):
 					print("")
				else:
					# else explain to the user to rerun
					print("\\text{\\todo[inline,color=red!40]{")
					print("No output of the The FormSkel tool, you need to run: (1) FormSkel and its generated Makefile; (2) pythonTEX and (3) pdflatex so to get the result of your Formula "+str(cptForm)+" of Section "+str(cptSection))
					print("}}")
		else:
			# The input does not exits so we must add it and explain that to the user
			fileFormToSkelIN = open(namefileIN, "w")
			fileFormToSkelIN.write(formula)
			fileFormToSkelIN.close()
			print("\\text{\\todo[inline,color=red!40]{")
			print("The generation of the input files for the FormSkel tools has been done; Please run (1) FormSkel and its generated Makefile; (2) pythonTEX and (3) pdflatex so to get the result of your Formula "+str(cptForm)+" of Section "+str(cptSection))
			print("}}")
	except (OSError, IOError) as e:
		print("\\text{\\todo[inline,color=red!40]{")
		if isDef:
			print("FormSkel-error: IO problem during formulaToSkel with the output file for section "+str(cptSection)+" definition "+str(nameDef))
		else:
			print("FormSkel-error: IO problem during formulaToSkel with the output file for section "+str(cptSection)+" formula "+str(cptForm))
		print("}}")
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		if isDef:
			print("FormSkel-error: formulaToSkel fail for section "+str(cptSection)+" definition "+str(nameDef))
		else:
			print("FormSkel-error: formulaToSkel fail for section "+str(cptSection)+" formula "+str(cptForm))
		print("}}")


def formulaToSkelBis(label,language,line):
	try:
		
		global cptSection
		global cptForm
		global cptDef

		#Read if it is a definition or not (a formula)
		namefileDEF = "./formSkel/defOrNot"
		fileDEF = open(namefileDEF, "r")
		isDef = (fileDEF.readline().strip())=="True"
		#Read the name is definition
		if isDef:
			nameDef = (fileDEF.readline().strip())
		fileDEF.close()

		# namefileLANG, which language is used for computing this formula
		if isDef:
			namefileLANG = "./formSkel/section"+str(cptSection)+".definition."+str(nameDef)+".formSkel.lang" 
		else:
			namefileLANG = "./formSkel/section"+str(cptSection)+".formula"+str(cptForm)+".formSkel.lang" 
		fileFormToSkelLANG = open(namefileLANG, "w")
		fileFormToSkelLANG.write(language+"\n")
		fileFormToSkelLANG.close()

		namefileAssocLabelNumber = "./formSkel/assocLabelNumber"
		# file not exist or firtst section ==> new file
		if not(os.path.exists(namefileAssocLabelNumber)) or (cptSection == 1):
			fileAssoc = open(namefileAssocLabelNumber,"w")
			fileAssoc.close()
		
		if not(isDef):
			# Format, section number, formula number, label number
			if label!="":
				fileASSOC = open(namefileAssocLabelNumber,"r")
				# Searching if not the same label
				lines = (list(fileASSOC))		
				for l in lines:
					data=l.strip().split(",")
					if data[2]==label:
						fileASSOC.close()
						raise Exception("Sorry, label still present")
				fileASSOC.close()
				# Finally, add the new label
				fileASSOC = open(namefileAssocLabelNumber,"a")
				fileASSOC.write(str(cptSection)+","+str(cptForm)+","+label+"\n")
				fileASSOC.close()
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		if isDef:
			print("FormSkel-error: formToSkel fail to create a new formula for section "+str(cptSection)+" definition "+str(nameDef)+" at line "+line+" of your LaTeX file")
		else:
			print("FormSkel-error: formToSkel fail to create a new formula for section "+str(cptSection)+" formula "+str(cptForm)+" at line "+line+" of your LaTeX file")
		print("}}")

# Return the formula's number and section if it is a label, otherwise, the form/section given as a parameter
def formAndSecWithLabel(form, section, label, intSection):
	fromForm = form
	fromSec = section
	#Si label vide alors on garde le numero de formule		
	if label=='':
		if section=="Current":
			fromSec=str(intSection)
	else:
		#Else, we check if it is a definition (check if the file exist)
		#Sinon on recherche le label et on le prend si on le trouve
		namefileAssocLabelNumber = "./formSkel/assocLabelNumber"
		fileASSOC = open(namefileAssocLabelNumber,"r")
		# Searching the same label
		lines = (list(fileASSOC))
		for l in lines:
			data=l.strip().split(",")
			if data[2]==label:
				fromSec = data[0]
				fromForm = data[1]
		fileASSOC.close()
	return fromSec, fromForm



######### Copying a formula from another section #########
def copyFormula(section,form,language,label,line,newlabel):
	try:
		global cptSection
		global cptForm

		cptForm = cptForm + 1

		fromSec, fromForm = formAndSecWithLabel(form,section,label,cptSection)
		
		#Copy the formula (file to file)
		nameFormToCopy = "./formSkel/section"+fromSec+".formula"+fromForm+".formSkel.in"
		nameFormNew = "./formSkel/section"+str(cptSection)+".formula"+str(cptForm)+".formSkel.in"
		shutil.copy2(nameFormToCopy,nameFormNew)
		
		#Write the wanted language
		nameFormNewLang = "./formSkel/section"+str(cptSection)+".formula"+str(cptForm)+".formSkel.lang"
		fileLang = open(nameFormNewLang, "w")
		fileLang.write(language+"\n")

		#Adding the new label
		namefileAssocLabelNumber = "./formSkel/assocLabelNumber"
		# file not exist or firtst section ==> new file
		if not(os.path.exists(namefileAssocLabelNumber)) or (cptSection == 1):
			fileAssoc = open(namefileAssocLabelNumber,"w")
			fileAssoc.close()

		fileASSOC = open(namefileAssocLabelNumber,"r")
		# Searching if not the same label
		lines = (list(fileASSOC))
		for l in lines:
			data=l.strip().split(",")
			if data[2]==newlabel:
				fileASSOC.close()
				raise Exception("Sorry, label still present")
		fileASSOC.close()
		# Finally, add the new label
		fileASSOC = open(namefileAssocLabelNumber,"a")
		fileASSOC.write(str(cptSection)+","+str(cptForm)+","+newlabel+"\n")
		fileASSOC.close()

		#Close and write the cptForm
		fileLang.close()
		fileCptForm = open(namefileCptForm, "w")
		fileCptForm.write(str(cptForm))
		fileCptForm.close()
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		print("FormSkel-error: copyFormula fail to create a new formula from section "+section+" formula "+form+" at line "+line)
		print("}}")



######### Adding a variable in the environment file of the tool #########
def formulaToSkelAddToDef(data,line):

	# Creating the directory to put the file if needed
	try:
		os.mkdir("formSkel")		
	except (OSError, IOError) as e:
		pass

	# Defining the global counter of section if needed
	global cptSection	

	# Adding the environment only if the first formula of the section does not exists 
	# (otherwise the formula have been computed previously)
	#namefileIN = "./formSkel/section"+str(cptSection)+".formula1.formSkel.in.tmp"

	# Delete the surrounding dollars 
	#data = (data[:-1])[1:]
	data = delDollarsAndPercent(data)

	#if (not (os.path.exists(namefileIN))):
	enviIN = open("./formSkel/environment.section"+str(cptSection)+".formSkel.in.tmp", "a") 
	enviIN.write(data)
	enviIN.write('\n')
	enviIN.close()


#TODO: much more try except to test all problems
# For example:
#  - nth not an integer or out-out-bound
#  - form not an integer or invalid number (not 0< or <numberOfForms(section))
#  - section not an integer or invalid number (not 0< or <numberOfSections)
#  - no nth line in the file
#  - etc.
######### Adding the result of formula (multi !) from tool #########
def formulaToSkelNthValue(secretId, secretIdVisible, section, maxSizeArg, maxDecimalArg, form, nth, proc, label, server, ServerDir, ServerAccess, ServerHTTP, lineLatex):
	try:
		global cptSection
		fromSec, fromForm = formAndSecWithLabel(form,section,label,str(cptSection))
		intSection = int(fromSec)
		intNth  = int(nth)-1
		intProc = int(proc)-1

		# First testing if the first line is "MULTI"
		namefileOUT = "./formSkel/section"+str(intSection)+".formula"+fromForm+".formSkel.out"		
		fileOUT = open(namefileOUT, "r")
		line= fileOUT.readline().strip()		
		if line=="MULTI":
			#result=(list(fileOUT))[intNth]
			#print("\\todo[inline,color=green!40]{")
			#print(result)
			#print("}")
			jsonFILE = open('config.json',"r")
			try:
				data = json.load(jsonFILE)
			except Exception as err:
				print("\\text{\\todo[inline,color=red!40]{")
				print("FormSkel-error: bad config.json file"+str(err))
				print("}}")
				return
			jsonFILE.close()
			sizeN = 0
			for s in data['environments']:
				if s['section']==intSection:
					# Find a list
					for name in s:
						if (isinstance(s[name], list)) and (name!="processors"):
							sizeN = len(s[name])
							break
					break
			if sizeN==0:
				print("\\text{\\todo[inline,color=red!40]{")
				print("FormToSkel-error1: no list of data in the section "+str(intSection)+" of config.json")
				print("}}")
				return
			listProcs = fileOUT.readline().strip().split(" ")
			nbNprocs = len(listProcs)
			lines=(list(fileOUT))
			if (intProc<len(listProcs) or intProc>=0):
				#whichIndex = listProcs[intProc]
				#print("intNth = "+str(intNth))
				#print("intProc = "+str(intProc))
				#print("sizeN = "+str(sizeN))
				#print(2*(intNth-1)+2*intProc*sizeN)
				link, result = dataOrLink(lines[2*(intNth)+2*intProc*sizeN])
				if link:					
					formulaToSkelPrintMarkingMarket(secretId, secretIdVisible, maxSizeArg, maxDecimalArg, result, server, ServerDir, ServerAccess, ServerHTTP, lineLatex)					
				else:
					print("\\textcolor{green}{")
					if (secretIdVisible=="true") or (secretIdVisible=="True"):
						print("\\href{http://secretId="+secretId+"/}{")
					printData(whichKindOfValue(result),result,int(maxDecimalArg))
					if (secretIdVisible=="true") or (secretIdVisible=="True"):
						print("}")
					print("}\\unskip")
			else:
				print("\\text{\\todo[inline,color=red!40]{")
				print("FormToSkel-error2: "+str(intProc)+" is not a nth valid number of processors of "+str(listProcs)+" at line "+lineLatex)
				print("}}")
		elif line=="ERROR":
			print("\\text{\\todo[inline,color=red!40]{")
			line = fileOUT.readline()
			print("FormSkel-error3: "+line+"for "+str(intSection)+" formula "+form+" for nth processor "+proc+" for nth processor "+proc+" "+nth+"th value at line "+lineLatex)
			print("}}")
		else:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error4: not a MULTI output file for section "+str(intSection)+" formula "+form+" for nth processor "+proc+" for nth processor "+proc+" "+nth+"th value at line "+lineLatex)
			print("}}")
		fileOUT.close()
	except (OSError, IOError) as e:
		print("\\text{\\todo[inline,color=red!40]{")
		print("FormSkel-error5: IO problem during formulaToSkelNthValue with the output file for section "+str(intSection)+" formula "+form+" for nth processor "+proc+" "+nth+"th value (surely the output file does not exists, you should run the formSkel Makefile)"+", problem at line "+lineLatex)
		print("}}")
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		print("FormSkel-error6: formulaToSkelNthValue fail for formula "+form+" for nth processor "+proc+" "+nth+"th value at line "+lineLatex)
		print("}}")


######### Adding the time of formula (multi !) from tool #########
def formulaToSkelNthTime(secretId, secretIdVisible, section, maxDecimalArg, form, nth, proc, timer, label, lineLatex):
	try:
		global cptSection
		fromSec, fromForm = formAndSecWithLabel(form,section,label,str(cptSection))
		intSection = int(fromSec)
		intNth = int(nth)-1
		intProc=int(proc)-1

		# First testing if the first line is "MULTI"
		namefileOUT = "./formSkel/section"+str(intSection)+".formula"+fromForm+".formSkel.out"		
		fileOUT = open(namefileOUT, "r")
		line= fileOUT.readline().strip()		
		if line=="MULTI":
			#result=(list(fileOUT))[intNth]
			#print("\\todo[inline,color=green!40]{")
			#print(result)
			#print("}")
			jsonFILE = open('config.json',"r")
			try:
				data = json.load(jsonFILE)
			except Exception as err:
				print("\\text{\\todo[inline,color=red!40]{")
				print("FormSkel-error: bad config.json file"+str(err))
				print("}}")
				return
			jsonFILE.close()
			sizeN = 0
			for s in data['environments']:
				if s['section']==intSection:
					# Find a list
					for name in s:
						if (isinstance(s[name], list)) and (name!="processors"):
							sizeN = len(s[name])
							break
					break
			if sizeN==0:
				print("\\text{\\todo[inline,color=red!40]{")
				print("FormToSkel-error: no list of data in te section "+str(intSection)+" of config.json")
				print("}}")
				return
			listProcs = fileOUT.readline().strip().split(" ")
			nbNprocs = len(listProcs)
			lines=(list(fileOUT))
			if (intProc<len(listProcs) or intProc>=0):
				if (secretIdVisible=="true") or (secretIdVisible=="True"):
					print("\\href{http://secretId="+secretId+"/}{")
				result = choiceOfTime(timer,lines[2*(intNth)+2*intProc*sizeN+1],maxDecimalArg)
				print("\\textcolor{green}{")
				print(result+"\\unskip")
				print("}")
				if (secretIdVisible=="true") or (secretIdVisible=="True"):
					print("}")
				print("\\unskip")
			else:
				print("\\text{\\todo[inline,color=red!40]{")
				print("FormToSkel-error: "+str(intProc)+" is not a nth valid number of processors of "+str(listProcs)+" at line "+lineLatex)
				print("}}")
		elif line=="ERROR":
			print("\\text{\\todo[inline,color=red!40]{")
			line = fileOUT.readline()
			print("FormSkel-error: "+line+"for "+str(intSection)+" formula "+form+" for nth processor "+proc+" "+nth+"th value at line "+lineLatex)
			print("}}")
		else:
			print("\\todo[inline,color=red!40]{")
			print("FormSkel-error: not a MULTI output file for section "+str(intSection)+" formula "+form+" for nth processor "+proc+" "+nth+"th value at line "+lineLatex)
			print("}")
		fileOUT.close()
	except (OSError, IOError) as e:
		print("\\text{\\todo[inline,color=red!40]{")
		print("FormSkel-error: IO problem during formulaToSkelNthTime with the output file for section "+str(intSection)+" formula "+form+" for nth processor "+proc+" "+nth+"th value (surely the output file does not exists, you should run the formSkel Makefile), problem at line "+lineLatex)
		print("}}")
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		print("FormSkel-error: formulaToSkelNthTime fail for formula "+form+" for nth processor "+proc+" "+nth+"th value"+" at line "+lineLatex)
		print("}}")

#TODO: Rationnal and other kind of values ! 
#Surely adding a new line in the file ".out" to read the type
def whichKindOfValue(result):
	try:
		a = int(result)
		return "integer"
	except Exception as e:
		try:
			a = float(result)
			return "real"
		except Exception as e:
			return "complex"

######### Adding the result of formula (solo) from tool #########
## TODO: Same problems as for nth
def formulaToSkelValue(secretId, secretIdVisible, section, maxSizeArg, maxDecimalArg, form, proc, label, server, ServerDir, ServerAccess, ServerHTTP, lineLatex):
	try:
		intProc=int(proc)-1
		global cptSection
		fromSec, fromForm = formAndSecWithLabel(form,section,label,str(cptSection))
		intSection = int(fromSec)
		namefileOUT = "./formSkel/section"+str(intSection)+".formula"+fromForm+".formSkel.out"
		fileOUT = open(namefileOUT, "r")
		line = fileOUT.readline().strip()
		if line=="SOLO":
 			#result=fileOUT.readline()
			#print("\\todo[inline,color=green!40]{")
			#print(result)
			#print("}")
			listProcs = fileOUT.readline().strip().split(",")
			nbNprocs = len(listProcs)
			lines=(list(fileOUT))
			#Testing the number of results
			if (len(lines)/2)!=nbNprocs:
				print("\\text{\\todo[inline,color=red!40]{")
				print("FormToSkel-error: the number of results is not equal to the different wanted numbers of processors; for ... at line "+lineLatex)
				print("}}")
			else:
				#Testing if the wanted nth number of processors is valid
				if (intProc<len(listProcs) or intProc>=0):
					link, result = dataOrLink(lines[2*intProc])
					if link:
						#print("\\textcolor{brown}{")
						formulaToSkelPrintMarkingMarket(maxSizeArg, maxDecimalArg, result, server, ServerDir, ServerAccess, ServerHTTP, lineLatex)
						#print("}\\unskip")
					else:
						if (secretIdVisible=="true") or (secretIdVisible=="True"):
							print("\\href{http://secretId="+secretId+"/}{")
						print("\\textcolor{green}{")
						printData(whichKindOfValue(result),result,int(maxDecimalArg))
						print("}")
						if (secretIdVisible=="true") or (secretIdVisible=="True"):
							print("}")
						print("\\unskip")
				else:
					print("\\text{\\todo[inline,color=red!40]{")
					print("FormToSkel-error: "+str(intProc)+" is not a nth valid number of processors of "+str(listProcs)+" at line "+lineLatex)
					print("}}")
		elif line=="ERROR":
			print("\\text{\\todo[inline,color=red!40]{")
			line = fileOUT.readline()
			print("FormSkel-error: "+line+"for "+str(intSection)+" formula "+form+" for nth processor "+proc)
			print("}}")
		else:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error: not a SOLO output file for section "+str(intSection)+" formula "+form+" for nth processor "+proc)
			print("}}")
		fileOUT.close()	
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		print("FormSkel-error: formulaToSkelValue fail for formula "+form+" for nth processor "+proc+" at line "+lineLatex)
		print("}}")


######### Adding the result of formula (solo) from tool #########
## TODO: Same problems as for nth
def formulaToSkelTime(secretId, secretIdVisible, section, maxDecimalArg, form, proc, timer, label, lineLatex):
	try:
		intProc=int(proc)-1
		global cptSection
		fromSec, fromForm = formAndSecWithLabel(form,section,label,str(cptSection))
		intSection = int(fromSec)
		
		# First testing if the first line is "SOLO"
		namefileOUT = "./formSkel/section"+str(intSection)+".formula"+fromForm+".formSkel.out"
		fileOUT = open(namefileOUT, "r")
		line = fileOUT.readline().strip()
		if line=="SOLO":
 			#result=fileOUT.readline()
			#print("\\todo[inline,color=green!40]{")
			#print(result)
			#print("}")
			listProcs = fileOUT.readline().strip().split(",")
			nbNprocs = len(listProcs)
			lines=(list(fileOUT))
			#Testing the number of results
			if (len(lines)/2)!=nbNprocs:
				print("\\todo[inline,color=red!40]{")
				print("FormToSkel-error: the number of results is not equal to the different wanted numbers of processors; for ..., problem at line "+lineLatex)
				print("}")
			else:
				#Testing if the wanted nth number of processors is in the list
				if (intProc<len(listProcs) or intProc>=0):
					#whichIndex = listProcs.index(proc)
					if (secretIdVisible=="true") or (secretIdVisible=="True"):
						print("\\href{http://secretId="+secretId+"/}{")
					result = choiceOfTime(timer,str(lines[2*intProc+1]),maxDecimalArg)
					print(result)
					if (secretIdVisible=="true") or (secretIdVisible=="True"):
						print("}")
					result = choiceOfTime(timer,str(lines[2*intProc+1]),maxDecimalArg)
					print("\\unskip")
				else:
					print("\\text{\\todo[inline,color=red!40]{")
					print("FormToSkel-error: "+str(intProc)+" is not a nth valid number of processors of "+str(listProcs)+" at line "+lineLatex)
					print("}}")
		elif line=="ERROR":
			print("\\text{\\todo[inline,color=red!40]{")
			line = fileOUT.readline()
			print("FormSkel-error: "+line+"for "+str(intSection)+" formula "+form+" for nth processor "+proc)
			print("}}")
		else:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error: not a SOLO output file for section "+str(intSection)+" formula "+form+" for nth processor "+proc)
			print("}}")
		fileOUT.close()		
	except (OSError, IOError) as e:
		print("\\text{\\todo[inline,color=red!40]{")
		print("FormSkel-error: IO problem during formulaToSkelTime with the output file for formula "+form+" for nth processor "+proc+" value (surely the output file does not exists, you should run the formSkel Makefile), problem at line "+lineLatex)
		print("}}")
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		print("FormSkel-error: formulaToSkelTime fail for formula "+form+" for nth processor "+proc+" at line "+lineLatex)
		print("}}")


######### Adding the nth number of processors #########
## TODO: Same problems as for nth
def formulaToSkelNthProc(secretId, secretIdVisible, section, nth, lineLatex):
	try:
		global cptSection
		if section=="Current":
			intSection = cptSection
		else:
			intSection = int(section)
		intNth=int(nth)-1
		jsonFILE = open('config.json',"r")		
		try:
			data = json.load(jsonFILE)
		except Exception as err:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error: bad config.json file"+str(err))
			print("}}")
			return
		# A single processor (default)
		jsonFILE.close()
		listProcs = [1]
		for s in data['environments']:
			if s['section']==intSection:
				# Find a list
				for name in s:
					if (isinstance(s[name], list)) and (name=="processors"):
						listProcs = (s[name])
						break
				break
		if (intNth<len(listProcs) or intNth>=0):
			if (secretIdVisible=="true") or (secretIdVisible=="True"):
				print("\\href{http://secretId="+secretId+"/}{")
			print(str(listProcs[intNth]))
			if (secretIdVisible=="true") or (secretIdVisible=="True"):
				print("}")
			print("\\unskip")
		else:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormToSkel-error: "+str(intNth)+" is not a nth valid number of processors of "+str(listProcs)+" at line "+lineLatex)
			print("}}")
	except (OSError, IOError) as e:
		print("\\text{\\todo[inline,color=red!40]{")
		print("FormSkel-error: IO problem during formulaToSkelTime with the output file  value (surely the output file does not exists, you should run the formSkel Makefile), problem at line "+lineLatex)
		print("}}")
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		print("FormSkel-error: formulaToSkelTime fail at line "+lineLatex)
		print("}}")


######### Give the value of SINGLE variable "n" of a specific section #########
def formulaToSkelParam(secretId, secretIdVisible, section, maxSizeArg, maxDecimalArg, n, Server, ServerDir, ServerAccess, ServerHTTP, lineLatex):
	try:
		global cptSection
		if section=="Current":
			intSection = cptSection
		else:
			intSection = int(section)
		jsonFILE = open('config.json',"r")		
		try:
			data = json.load(jsonFILE)
		except Exception as err:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error: bad config.json file"+str(err))
			print("}}")
			return		
		for s in data['environments']:
			if s['section']==intSection:				
				if type(s[n]) is dict:
					formulaToSkelPrintMarkingMarket(maxSizeArg, maxDecimalArg, str((s[n])['file']), Server, ServerDir, ServerAccess, ServerHTTP, lineLatex)
				elif type(s[n]) is list:
					raise Exception("It looks like a list not a value, please considering the appropriate LaTex commands")
				else:
					if (secretIdVisible=="true") or (secretIdVisible=="True"):
						print("\\href{http://secretId="+secretId+"/}{")
					print(str(s[n]))
					if (secretIdVisible=="true") or (secretIdVisible=="True"):
						print("}")
					print("\\unskip")
				break
		jsonFILE.close()
	except (OSError, IOError) as e:
		print("\\text{\\todo[inline,color=red!40]{")
		print("FormSkel-error: IO problem during formulaToSkelParam of variable "+n+" (surely the output file does not exists, you should run the formSkel Makefile), problem at line "+lineLatex)
		print("}}")
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		print("FormSkel-error: formulaToSkelParam fail of variable "+n+" line "+lineLatex)
		print("}}")

######### Give the nth value of MULTI variable "n" of a specific section #########
def formulaToSkelNth(secretId, secretIdVisible, section, maxSizeArg, maxDecimalArg, n, nth, Server, ServerDir, ServerAccess, ServerHTTP, lineLatex):
	try:
		intNth = int(nth)-1
		global cptSection
		if section=="Current":
			intSection = cptSection
		else:
			intSection = int(section)			
		jsonFILE = open('config.json',"r")
		try:
			data = json.load(jsonFILE)
		except Exception as err:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error: bad config.json file"+str(err))
			print("}}")
			return		
		for s in data['environments']:
			if s['section']==intSection:
				if type(s[n][intNth]) is dict:
					formulaToSkelPrintMarkingMarket(maxSizeArg, maxDecimalArg, str(s[n][intNth]['file']), Server, ServerDir, ServerAccess, ServerHTTP, lineLatex)
				else:
					if (secretIdVisible=="true") or (secretIdVisible=="True"):
						print("\\href{http://secretId="+secretId+"/}{")
					print(str(s[n][intNth]))
					if (secretIdVisible=="true") or (secretIdVisible=="True"):
						print("}")
					print("\\unskip")
				break
		jsonFILE.close()
	except (OSError, IOError) as e:
		print("\\text{\\todo[inline,color=red!40]{")
		print("FormSkel-error: IO problem during formulaToSkelNth of variable "+n+" for its  "+nth+"th value (surely the output file does not exists, you should run the formSkel Makefile), problem at line "+lineLatex)
		print("}}")
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		print("FormSkel-error: formulaToSkelNth fail for section of variable "+n+" for its  "+nth+"th value at line "+lineLatex)
		print("}}")

def convertHex(what):
	try:
		return float(what)
	except:
		return float.fromhex(what)

def quantizeRec(maxDecimal):
	if maxDecimal<=1:
		return '1'
	else:
		return '0'+quantizeRec(maxDecimal-1)

def quantize(maxDecimal):
	if maxDecimal>26:
		return '0.'+quantizeRec(26)
	return '0.'+quantizeRec(maxDecimal)

def printData(kind, whatToPrint, quantize):
	if kind=="integer":
		sys.stdout.write(str(int(whatToPrint)))
	elif kind=="real":
		#'{:.2f}'.format(res)
		res=convertHex(whatToPrint)
		if quantize==-1:
			#sys.stdout.write(str(Decimal(res)))
			sys.stdout.write(('{:.60g}').format(res))
		else:
			sys.stdout.write(('{:.'+str(quantize)+'f}').format(res))
			#sys.stdout.write(str(res.quantize(quantize, rounding=ROUND_DOWN)))
	elif kind=="complex":
		if whatToPrint=="0":
			sys.stdout.write("0")
		else:
			res = whatToPrint.split()
			re = convertHex(res[0])
			im = convertHex(res[1])
			if quantize==-1:
				sys.stdout.write(('{:.60g}').format(re)+"+"+('{:.60g}').format(im)+"i")
			else:
				sys.stdout.write(('{:.'+str(quantize)+'f}').format(re)+"+"+('{:.'+str(quantize)+'f}').format(im)+"i")

#Print a matrix
def formulaToSkelPrintMarkingMarketFromFile(secretId, secretIdVisible, maxSizeArg, maxDecimalArg, file, filename, pathAndFilename):
	maxSize = int(maxSizeArg)
	maxDecimal = int(maxDecimalArg)	
	beginningMat = False
	beginningAngle = False
	try:
		# Read the first line
		items = file.readline().strip().split()
		#Every thing in lower caracteres
		for i in range(len(items)): 
			items[i] = items[i].lower()
		# Testing the keywords
		if items[0]!="%%matrixmarket":
			print("\\text{\\todo[inline,color=red!40]{")			
			print("FormSkel-error: "+filename+" is not a good MatrixMarket format, miss %%MatrixMarket, problem at line "+lineLatex)
			print("}}")
			return ""
		if items[1]=="matrix":
			kind=items[1]
		elif items[1]=="vector":
			kind=items[1]
		elif items[1]=="covector":
			kind=items[1]
		else:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error: "+filename+" is not a good MatrixMarket format, not a vector, covector or matrix, problem at line "+lineLatex)
			print("}}")
			return ""
		if items[2]=="array":
			myRead=items[2]
		elif items[2]=="coordinate":
			myRead=items[2]
		else:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error: "+filename+" is not a good MatrixMarket format, not a coordinate nor array reading, problem at line "+lineLatex)
			print("}}")
			return ""
		if items[3]=="real":
			myData=items[3]
		elif items[3]=="complex":
			myData=items[3]
		elif items[3]=="integer":
			myData=items[3]
		else:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error: "+filename+" is not a good MatrixMarket format, not a real, complex or integer, problem at line "+lineLatex)
			print("}}")
			return ""
		if items[4]=="general":
			myForm=items[4]
		elif items[4]=="symmetric":
			myForm=items[3]
		elif items[4]=="skew-symmetric":
			myForm=items[4]
		else:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error: "+filename+" is not a good MatrixMarket format, not a symmetric, general, skew-symmetric (hermitian not yet implemented), problem at line "+lineLatex)
			print("}}")
			return ""
		if (kind=="vector") or (kind=="covector"):
			if (myForm!="general"):
				print("\\text{\\todo[inline,color=red!40]{")
				print("FormSkel-error: "+filename+" is not a good MatrixMarket format, a (CO)VECTOR could not be symmetric, skew or hermetian), problem at line "+lineLatex)
				print("}}")
				return ""
		if (myRead=="array"):
			if (myForm!="general"):
				print("\\text{\\todo[inline,color=red!40]{")
				print("FormSkel-error: "+filename+" is not a good MatrixMarket format, a array format could not be symmetric, skew or hermetian), problem at line "+lineLatex)
				print("}}")
				return ""
		# Ignoring the first comments 
		line = file.readline().strip()
		while (line[0]=='%'):
				line = file.readline().strip()
		dataSizes = line.strip().split()
		numLines = 0
		numColumns = 0
		numRows = 0
		if kind=="vector":
			numColumns = int(dataSizes[0])
			if myRead=="array":
				numLines = numColumns
			if myRead=="coordinate":
				numLines = int(dataSizes[1])
		elif kind=="covector":
			numRows = int(dataSizes[0])
			if myRead=="array":
				numLines = numRows
			if myRead=="coordinate":
				numLines = int(dataSizes[1])
		elif kind=="matrix":
			numRows = int(dataSizes[0])
			numColumns = int(dataSizes[1])
			if myRead=="array":
				numLines = numRows * numColumns
			if myRead=="coordinate":
				numLines = int(dataSizes[2])		
		if (kind=="matrix"):
			if (numColumns>maxSize) or (numRows>maxSize):
				#print("\\todo[inline,color=red!40]{")
				#print("FormSkel-error: "+filename+" is too big to be print ! (columns or rows greater than "+str(maxSize)+" elements), problem at line "+lineLatex)
				#print("}")
				#print("\\text{\\url{"+Server+":"+ServerDir+"/"+filename+"}}")
				print("\\textcolor{brown}{")
				return ("\\text{\\href{"+pathAndFilename+"}{"+filename+"}}}\\unskip")
		else:
			if (numLines>maxSize) or (numColumns>maxSize) or (numRows>maxSize):
				#print("\\todo[inline,color=red!40]{")
				#print("FormSkel-error: "+filename+" is too big to be print ! (greater than "+str(maxSize)+" elements), problem at line "+lineLatex)
				#print("}")
				#print("\\text{\\url{"+Server+":"+ServerDir+"/"+filename+"}}")
				print("\\textcolor{brown}{")
				return ("\\text{\\href{"+pathAndFilename+"}{"+filename+"}}}\\unskip")
		#Reading the data		
		# ##################################
		# Vectors
		# ##################################
		if kind=="vector":
			if (secretIdVisible=="true") or (secretIdVisible=="True"):
				sys.stdout.write("\\href{http://secretId="+secretId+"/}{")
			sys.stdout.write("\\left[")
			beginningAngle = True
			if myRead=="array":
				# ARRAY DATA
				for x in range(numLines):
					whatToPrint = file.readline().strip()
					printData(myData,whatToPrint,maxDecimal)
					if x!=numLines-1:
						sys.stdout.write(", \\ ")
			else:
				# COORDINATE DATA
				vec = {}
				for x in range(numLines):
					data = file.readline().strip().split()
					vec[int(data[0])-1] = ' '.join(data[1:])
				for x in range(numColumns):
					if x in vec:
						printData(myData,vec[x],maxDecimal)
					else:
						printData(myData,"0",maxDecimal)
					if x!=numColumns-1:
						sys.stdout.write(", \\ ")
			sys.stdout.write(" \\right]")
			if (secretIdVisible=="true") or (secretIdVisible=="True"):
				sys.stdout.write("}")
		# ##################################
		#CoVectors
		# ##################################
		elif kind=="covector":
			if (secretIdVisible=="true") or (secretIdVisible=="True"):
				sys.stdout.write("\\href{http://secretId="+secretId+"/}{")
			print("\\left[")
			beginningAngle = True
			print("\\hspace*{-0.5mm}")
			print("\\begin{array}{l}")
			beginningMat = True
			if myRead=="array":
				# ARRAY DATA
				for x in range(numLines):
					whatToPrint = file.readline().strip()
					printData(myData,whatToPrint,maxDecimal)
					if x!=numLines-1:
						print("\\\\")
			else:
				# COORDINATE DATA
				vec = {}
				for x in range(numLines):
					data = file.readline().strip().split()
					vec[int(data[0])-1] = ' '.join(data[1:])
				for x in range(numRows):
					if x in vec:
						printData(myData,vec[x],maxDecimal)
					else:
						printData(myData,"0",maxDecimal)
					if x!=numRows-1:
						print("\\\\")
			print("")
			print("\\end{array}")
			print("\\hspace*{-2mm}")
			sys.stdout.write("\\right]")
			if (secretIdVisible=="true") or (secretIdVisible=="True"):
				sys.stdout.write("}")
		# ##################################
		# Matrix
		# ##################################
		elif kind=="matrix":
			if (secretIdVisible=="true") or (secretIdVisible=="True"):
				sys.stdout.write("\\href{http://secretId="+secretId+"/}{")			
			print("\\left(")
			beginningAngle = True
			print("\\begin{array}{"+("l"*numColumns)+"}")
			beginningMat = True			
			if myRead=="array":				
				# ARRAY DATA
				mat = {}
				for y in range(numColumns):
					for x in range(numRows):
						data = file.readline().strip()
						mat[(x,y)] = data
				for x in range(numRows):
					for y in range(numColumns):
						#sys.stdout.write(mat[x,y])
						printData(myData,mat[x,y],maxDecimal)
						if y!=numColumns-1:
							sys.stdout.write(" & ")	
					if (x!=numRows-1):
						print("\\\\")
			else:				
				# COORDINATE DATA				
				mat = {}
				for x in range(numLines):
					data = file.readline().strip().split()
					if myForm=="general":
						mat[(int(data[0])-1,int(data[1])-1)] = ' '.join(data[2:])	
					elif myForm=="symmetric":
						r=int(data[0])-1
						c=int(data[1])-1
						mat[(r,c)] = ' '.join(data[2:])
						mat[(c,r)] = ' '.join(data[2:])
					elif myForm=="skew-symmetric":
						r=int(data[0])-1
						c=int(data[1])-1
						mat[(r,c)] = ' '.join(data[2:])
						mat[(c,r)] = '-'.join(data[2:])
				for x in range(numRows):
					for y in range(numColumns):
						if (x,y) in mat:
							printData(myData,mat[x,y],maxDecimal)
						else:
							printData(myData,"0",maxDecimal)
						if y!=numColumns-1:
							sys.stdout.write(" & ")	
						if (y==numRows-1) and (x!=numRows-1):
							print("\\\\")
			print("")
			print("\\end{array}")
			sys.stdout.write("\\right)")
			if (secretIdVisible=="true") or (secretIdVisible=="True"):
				sys.stdout.write("}")
			return ""
	except (OSError, IOError) as e:
		if beginningMat:
			print("\\end{array}")
		if beginningAngle:
			sys.stdout.write("\\right.")
			if (secretIdVisible=="true") or (secretIdVisible=="True"):
				sys.stdout.write("}")
		print("\\text{\\todo[inline,color=red!40]{")
		print("FormSkel-error: IO problem during formulaToSkelPrintMarkingMarket with the input file "+filename+", problem at line "+lineLatex)
		print("}}")
		return ""
	except Exception as exc:
		if beginningMat:
			print("\\end{array}")
		if beginningAngle:
			sys.stdout.write("\\right.")
			if (secretIdVisible=="true") or (secretIdVisible=="True"):
				sys.stdout.write("}")
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		print("FormSkel-error: formulaToSkelPrintMarkingMarket fail with the input file "+filename+", problem at line "+lineLatex)
		print("}}")
		return ""


def formulaToSkelPrintMarkingMarket(secretId, secretIdVisible, maxSizeArg, maxDecimalArg, filename, Server, ServerDir, ServerAccess, ServerHTTP, lineLatex):
	try:
		ssh = subprocess.Popen(['ssh', Server, 'cat', ServerAccess+"/"+filename], stdout=subprocess.PIPE)
		file = ssh.stdout
		res = formulaToSkelPrintMarkingMarketFromFile(secretId, secretIdVisible, maxSizeArg, maxDecimalArg, file, filename, ServerHTTP+"/"+filename)
		if res!="":
			print(res)
		file.close()
	except (OSError, IOError) as e:
		print("\\text{\\todo[inline,color=red!40]{")
		print("FormSkel-error: IO (open or access) problem during formulaToSkelPrintMarkingMarket with the input file "+filename+", problem at line "+lineLatex)
		print("}}")
	except Exception as exc:
		print("\\text{\\todo[inline,color=red!40]{")
		print(exc)
		print("FormSkel-error: formulaToSkelPrintMarkingMarket fail with the input file "+filename+", problem at line "+lineLatex)
		print("}}")

# TODO: utiliser un Decoder pour LaTex, , cls=LatexDecoder)
# Remplacer les { par des \{ et les tabulations par des \hspace
def formulaToSkelPrintEnv(section, lineLatex):
	try:
		global cptSection
		if section=="Current":
			intSection = cptSection
		elif section=="All":
			intSection = 0
		else:
			try:
				intSection = int(section)
			except:
				#Warning it is thus not an integer ^^
				intSection = section
		jsonFILE = open('config.json',"r")
		try:
			data = json.load(jsonFILE)
		except Exception as err:
			print("\\text{\\todo[inline,color=red!40]{")
			print("FormSkel-error: bad config.json file"+str(err))
			print("}}")
			return
		if (intSection=="letters") or  (intSection=="imports") or (intSection=="functions"):
			print("\\begin{verbatim}")
			print(json.dumps(data[intSection], indent=2, sort_keys=True, separators=("", ": ")))
			print("\\end{verbatim}")
			return
		if intSection==0:
			print("\\begin{verbatim}")
			print(json.dumps(data, indent=2, sort_keys=True, separators=("", ": ")))
			print("\\end{verbatim}")
			return
		for s in data['environments']:
			if s['section']==intSection:
				print("\\begin{verbatim}")
				print(json.dumps(s, indent=2, sort_keys=True, separators=("", ": ")))
				print("\\end{verbatim}")
				break
		jsonFILE.close()
	except (OSError, IOError) as e:
		print("\\text{\\todo[inline,color=red!40]{")
		print("FormSkel-error: IO problem (mainly lack of the config.json file or corruped file) during formulaToSkelPrintEnv for section "+str(intSection)+", problem at line "+lineLatex)
		print("}}")
	except:
		print("\\text{\\todo[inline,color=red!40]{")
		print("FormSkel-error: formulaToSkelPrintEnv fail for section "+str(intSection)+" at line "+lineLatex)
		print("}}")


#formulaToSkelPrintMarkingMarket(10,2,"vec.txt")

#pip install json2latex,
#import json2latex
#data = json.load(open('config.json',"r"))
#print(json2latex.dumps('printJSONN', data['environments']))