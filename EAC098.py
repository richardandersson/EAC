#!/usr/bin/env python
#-*- coding: utf-8 -*-

myversion = 'v0.98' #

## To do: ##
# Vectorize overlap calculations? Slow if there is a lot of data. Remember to make reference plots before fiddling.
# Add extra reliability calculation? Cohen's Kappa? That takes into consideration blank space / non-events?
# Ability to save image if people can't be bothered to do a screenshot, or want higher resolution?

#### CHANGES ####
# v. 0.98 (2013-04-22)
# - Changed all version numbers retroactively to better prepare for publication.
# - minor adjustments and tweaks. 
# - tweaks for speed.
#
# v.0.7 ()
# - Added ability to adjust ELAN's inter-rater reliability check with a time-weighted procedure.
# - New tabbed look, with possilibities to expand tool with other functions.
# - Possibility to graph two curves at once, for easy visual contrasting.
#
# v.0.6 (2012-03-28):
# - Now handles the prevention of "double-dipping" data when two adjacent analysis windows overlap. Also fixed two critical bugs which 
#   resulted in analysis windows not being triggered correctly. This was a problem for analyses relying too much on the shape of a single
#   curve, rather than comparing between two controlled conditions (where the curve would be "equally wrong" for both and thus not 
#   introducing a bias for or against any hypotheses). The program is now thoroughly validated against manually calculated and known
#   events.
# - Fixed cross-platform issues with divider lines.
# - Window size is now stored in settings.ini between sessions.
#
# v.0.5 (2012-03-17):
# - variable resolution and bin size, bin functions, separate settings dialog, stores user settings, and more.
#
# v.0.4:
# - can now load data files stored on network drives
#
# v.0.3:
# - minor fixes, such as more graceful handling of the situation when selected tiers or events can't be found in the files.
# - clears the graph area before analysis, in case something breaks, to not trick the user into believing the graph is true
#  when it is in fact old.
#
# v.0.2:
# - handles analysis window expanding beyond the limits of the annotation time line, using NaNs.
# This should now not inflate the number of zeros (but beware heterogeneity of variance).
#
# v.0.1:
# - now handles tier and events named with regular expression meta characters.
# - now handles both "alignable" annotations and "connected" annotations.

##### KNOWN ISSUES #####
# 1. This program is not really intended for using utterance-annotations as predictors, as they are often unique.
# Therefore, some bugs related to this exists, e.g. clipping the# length of 
# annotations and the max number of items in the drop-down menus.
#

#### READ ME! ####
# Tested under Windows 7 Ultimate 64, Ubuntu 10.04, 11.04 and 12:10.
# The program authors do not claim responsibility for any damages caused by this software.
# Use it on your own risk and make sure you have backed up the original files.
# The program is published under a GNU GPL 2.0 license.
# Attribute by citing the paper presenting this tool:
# Andersson, R. & Sandgren, O. (In preparation). "ELAN Analysis Companion (EAC): A Software Tool for Time-course Analysis of ELAN-annotated Data".
#
# Contact: richard[dot]andersson[AT]humlab[dot]lu[dot]se
#
# The code is not optimized in any way, and may be slow or consume large amounts of memory for
# large data sets. At least, this increases the chance that future versions will be better...

#### DEPENDENCIES ####
# * matplotlib
# * Numpy
###################

# IMPORTED PACKAGES
import os
import Tkinter as tk
import tkMessageBox
import tkFileDialog
import re
import numpy
import matplotlib.pyplot as plt
#import matplotlib
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg #, NavigationToolbar2TkAgg
from matplotlib.figure import Figure
import math
from datetime import datetime
#import copy
#import sys

#timeslots = dict() # holds look-up table of all time slots
global FOLDERFILE
FOLDERFILE = ''
global filenames
filenames = []
global tdd1_options
global dd1_count # obsolete?
global results
results = []
#global resultsbin
#global plotresults
#plotresults = []
global f # matplotlib canvas to be tk-embedded.
global a # matplotlib subplot
global res
res = 10
global overlapfunc
overlapfunc = "Double-dipping"
global binsize
binsize = 100
global binfunc
binfunc = "Mean"
global winsize
winsize = 3000
tierdefault = "select tier"
eventdefault = "select tier event"
onoffdefault = "select onset/offset"
tabstate = 'tca' # default: time-course analysis; irr = inter-rater reliability
IRRFOLDERFILE = ''
irrfilenames = ''
IRRdata = {} # hash with filenames holding complete irr file data



# load default values for variables
def loadsettings(*args): # list of strings of settings we want to load
    returnvals = []
    try:
        with open('ETC_settings.ini') as x:
            vars = [line.strip() for line in x.readlines()]
#            vars = [line.strip(['\s\n']) for line in x.readlines()]
            tempdict = {}
            for var in vars: # extract all setting names and their values
                i,j = var.split(':')
                tempdict[i] = j
                if j.isdigit(): # convert from string if it is a numeric value
                    tempdict[i] = int(j)
        for arg in args: # get all values requested by the function arguments
            returnvals.append(tempdict[arg])
        returnvals = tuple(returnvals) # convert list to tuple to match the expected output form
        return returnvals
    except IOError: # if the file does not exist...
        print("loadsettings() threw an IOError exception")
        pass # return nothing and trigger an exception


# enter time table information based info in elan file
def timetable(filename):
    timeslots = {}
    with open(filename) as x: f = x.read()
    pattern = re.compile('(?<=TIME_SLOT_ID=")\w+?(?=" TIME_VALUE=")')
    time_ids = re.findall(pattern, f) # get all id values
    pattern = re.compile('(?<= TIME_VALUE=")\d+(?="/>)')
    time_points = re.findall(pattern, f) # get all corresponding time values

    if len(time_ids) != len(time_points): # just checking
        raise Exception("Regular expression problem? IDs not matching up with slots.")
    for i in range(len(time_ids)): # now lets save the data in a look-up table (here: dict)
        timeslots[time_ids[i]] = int(time_points[i])
    ref2id = {}
    with open(filename) as x: f = x.read() # lets collect all alignable annotations with time points
    pattern = re.compile('<ALIGNABLE_ANNOTATION ANNOTATION_ID="(\w+)" TIME_SLOT_REF1="(\w+)" TIME_SLOT_REF2="(\w+)">')
    matches = re.findall(pattern, f)
    for a_match in matches:
        ref2id[a_match[0]] = [timeslots[a_match[1]], timeslots[a_match[2]]]
    with open(filename) as x: f = x.read() # now collect all referenced (connected) annotations with time
    pattern = re.compile('<REF_ANNOTATION ANNOTATION_ID="(\w+)" ANNOTATION_REF="(\w+)">')
    matches = re.findall(pattern, f)
    for a_match in matches:
        ref2id[a_match[0]] = ref2id[a_match[1]]
    return ref2id # dict(id), returns list with time_onset and time_offset

# taking the mean of _matrices_ containing NaNs
def nanmean(dat, dim):
    '''Taking the mean of a 2D numpy array containing nan:s.'''
    if dat.ndim != 2:
        raise TypeError("Function 'nanmean' should receive 2D arrays!")
    masked = numpy.ma.masked_array(dat,numpy.isnan(dat))
    maskedmean = numpy.mean(masked, dim)
    maskedmean = maskedmean.filled(numpy.nan)
    return maskedmean

# initialize with NaNs
def nans(shape, dtype=float):
    '''Initializing a numpy array of nan:s, given shape'''
    a = numpy.empty(shape, dtype)
    a.fill(numpy.nan)
    return a

# Find the max value in a dict with 2-element tuples/lists
def dictTupleMax(dictTuple):
    '''Return maximum value of second value of a 2-element tuple/list.'''
    maxvalue = 0
    for val in dictTuple.values():
        if val[1]>maxvalue:
            maxvalue = val[1]
    return maxvalue

def loadButtonFunc(): # bound to load button
    global FOLDERFILE
    global IRRFOLDERFILE
    if tabstate == 'tca':
        mainfile = tkFileDialog.askopenfilename(filetypes=[("ELAN files",'*.eaf'),("All files", "*.*")], title='Open ELAN file')
        if len(mainfile) > 0:
            FOLDERFILE = mainfile
    elif tabstate == 'irr':
        mainfile = tkFileDialog.askopenfilename(filetypes=[("ELAN inter-rater exports",'*.txt'),("All files", "*.*")], title='Open ELAN inter-rater exported file')
        if len(mainfile) > 0:
            IRRFOLDERFILE = mainfile
    loadFolder()

# select folder to process
def loadFolder(): # called by loadButtonFunc, but also bound to tickbox
    global filenames
    global irrfilenames
    global FOLDERFILE # I need this in order to modify the FOLDERFILE variable created in main
    global IRRFOLDERFILE
    global tdd11_options
    global tdd11_var
    global tierdropdown11
    global tdd12_options
    global tdd12_var
    
    if tabstate == 'tca':
        mainfile = FOLDERFILE
    elif tabstate == 'irr':
        mainfile = IRRFOLDERFILE
    if len(mainfile) == 0:
        return
    elif len(mainfile) > 0: # something is loaded
        tempfilenames = []
        tempfilenames = getFiles(mainfile)
        print("File(s) loaded:")
        for i in tempfilenames: print(i)
        if tabstate == 'tca':
#            print(type(tdd11_options))
#            print(type(tdd11_var))
#            print(type(tierdropdown11))
            prepTiers(tempfilenames, tierdropdown11, tierdropdown12) # Prepping predictor 1
            prepTiers(tempfilenames, tierdropdown21, tierdropdown22) # Prepping predictor 2
            prepTiers(tempfilenames, tierdropdown3, tierdropdown4) # Prepping dependent variable 
            # A note: currently empties dropdowns. Annoying if you do a test one a single file and then want to repeat for all files (menus empty)
    else:
        raise Exception("No proper file or folder specified")
    if tabstate == 'tca':
        FOLDERFILE = mainfile
        filenames = tempfilenames
    elif tabstate == 'irr':
        IRRFOLDERFILE = mainfile
        irrfilenames = tempfilenames


def splitPath(filewithpath):
    folders = re.search(r'.*?([\w :.-]+$)', filewithpath) # get the path (everything but the last filename in the path)
    path = folders.group(0)[0:len(folders.group(0))-len(folders.group(1))]
    filename = re.findall('[^.]+' ,folders.group(1))[0] # filename without extension
    extension = re.findall('\.[\w]+$' ,folders.group(1))[0][1:] # extension without dot
    return path, filename, extension

def getFiles(mainfile): # load one or several files and set file status field, return list of filenames
    filenames = []
    # file_and_folder_name (load), tickvar (to know whether to load entire folder)
    #if tabstate == 'tca':
#    print("Function getFiles() invoked")
    if len(mainfile) == 0: # if no main file is loaded, it should not come this far
        raise Exception("No file loaded and information was erroneously passed to getFiles()")
    elif tickvar.get() == 1 and '.' in mainfile[-4:]: # If box is ticked and main file has a max 3 character file extension
        mypath, fname, extension = splitPath(mainfile)
        fileobjects = os.listdir(mypath)
        for fs in fileobjects:
            if '_corrected.' in fs:
                continue # skip files with the "_corrected" suffix in the file name
            try:
                if re.match('[\w -.]+.' + extension + '$', fs).group() != None:
                    filenames.append(mypath + fs)
#                    print(mypath + fs) # print for verification purposes
            except AttributeError:
                print("No other files with that file extension were found")
        if tabstate == 'irr':
            irrfilevar.set(str(len(filenames)) + " " + extension + "-files loaded!")
            irrstatvar.set('''Press "Analyze!" to start''')
    elif tickvar.get() == 0: # If box is not ticked
        filenames.append(mainfile) # just get that single filename
        if tabstate == 'irr':
            irrfilevar.set(mainfile)
            irrstatvar.set('''Press "Analyze!" to start''')
    else:
        raise Exception("You opted to search in a folder based on an unidentified file extension. It is likely a bug if you see this error message...")
    return filenames


def prepTiers(datafiles, tiermenu_obj, eventmenu_obj): #, tierdd_objtier_options, tier_var, tierdd_obj
    f = tiermenu_obj.cget('textvariable') # get StringVar NAME (a separately set property)
    eval(f + ".set('" + tierdefault + "')") # update StringVar value which will change menu label
    f = eventmenu_obj.cget('textvariable') # get StringVar NAME (a separately set property)
    eval(f + ".set('" + eventdefault + "')") # update StringVar value which will change menu label    
    pattern = re.compile('(?<=TIER_ID=").+?(?=">)') # extract tier IDs
    tier_ids = []
    for fname in datafiles:
#        print(fname)
        with open(fname) as x: f = x.read() # open files and extract all tier ids.
        tier_ids.extend(re.findall(pattern, f)) # collect all tier ids in the files
    tier_ids = list(set(tier_ids)) # uniqueify the list of events
#    print("list of tier IDs:")
#    print(tier_ids)
    m = tiermenu_obj.children['menu']
    m.delete(0, 'end') # remove all menu items
#    print("all deleted")
    for val in tier_ids:  # for all tier ids
        m.add_command(label=val,command=lambda \
            name=val, obj=tiermenu_obj: dropdownFunction(name, obj, child=eventmenu_obj, filenames = datafiles)) #prepEvents(val, tier_var, tiermenu_obj, eventmenu_obj)) # set commands for options
        # if item on list is selected, it triggers the setting of options in the event dropdown.
    #return tier_options#, tier_var, tierdd_obj
    
def dropdownFunction(label, dd_obj, **kwargs): # label is the text to set on DD-function when selecting an item. dd_obj is the actual dropdown object.
    # keywords: child, filenames
#    sys.stdout.write("DDlabel: " + label + '\n')
    f = dd_obj.cget('textvariable') # get StringVar NAME (a separately set property)
    eval(f + ".set('" + label + "')") # update StringVar value which will change menu label
    if len(kwargs) == 0: # if no optional arguments (main tier)
        pass
    elif len(kwargs) == 2: # if OPTIONAL ARGUMENTS FOR A CHILD MENU ARE PASSED
        # do recursive magic
        events = getEvents(kwargs['filenames'], label)
        if kwargs['child'] not in events: # If we change tier but have already an (old) event selected)
            f = kwargs['child'].cget('textvariable') # get StringVar NAME (a separately set property)
            eval(f + ".set('" + eventdefault + "')") # update StringVar value which will change menu label            
        m = kwargs['child'].children['menu'] # get options of child menu
        m.delete(0, 'end') # remove options
        for event in events:
            m.add_command(label=event, command=lambda \
                name=event, obj=kwargs['child']: dropdownFunction(name, obj))
    else:
        raise Exception("No support for multiple child menus!")

def getEvents(datafiles, value): # extract events from ELAN annotation files, given a tier name
    pattern = re.compile('(?<=TIER_ID="' + re.escape(value) + '">).+?(?=</TIER>)' , re.DOTALL) # label = item
    all_tiers = []
    for fname in filenames: # for all our files
        with open(fname) as x: f = x.read() # collect all target tiers
        f = re.search(pattern, f)
        if f == None:
            continue
        all_tiers.append(f.group())
    pattern = re.compile('(?<=<ANNOTATION_VALUE>).+?(?=</ANNOTATION_VALUE>)') # find all tier events
    events = []
    for tier in all_tiers:
        events.extend(re.findall(pattern, tier)) # extract all events in that tier, in a list.
    events = list(set(events)) # uniqueify the list of events
#    for item in events:
#        print("Event:")
#        print(item)
    if len(events)>20:
        events = events[0:20] # max 20 unique events in list (typically clips utterance unique transcriptions)
    for event in events:
        if len(event)>20: # if event description is longer than 20 characters.
            events.remove(event)
            events.append(event[0:20]) # clips length of event to first 20 characters.    
    return events


def dummyfunc(*args):
    '''Just a testing function. Dumps output to console'''
    print(len(args))
    for arg in args:
        print(arg)
        
def dumpData(mystring):
    '''Just a testing function. Dumps output to file'''
    with open('dump.txt', 'w') as fs: fs.write(mystring)

def testwait(astring):
    '''Just a testing function. Halts program until keypress + ENTER.'''
    print(astring)
    f = raw_input() # Ignore warning

def quit(root):
    root.destroy()


def analyzeFiles(): # bound to Analyze!-button
    if tabstate == 'tca':
        processTCA()
    elif tabstate == 'irr':
        processIRR()

def processIRR(): # perform time-weighted interrater reliability analysis
    global IRRdata # global storing of all irr data
    IRRdata = {} # resetting global store
    oldIRRlist = [] # stores average irr for old calculation
    newIRRlist = [] # stores average irr for new calculation
    for irrfile in irrfilenames: # note that all files with "_corrected." in file name are skipped
        IRRdata[irrfile] = []
        with open(irrfile) as fid:
            overlap = []
            duration = []
            for line in fid:
                dataline = line.strip().split('\t')
                IRRdata[irrfile].append(line)
                if len(dataline) < 9: # if line is shorter than expected
                    continue # continue to next line
                if dataline[1] == '-': # if only second annotator has event
                    dataline[7] = str(int(dataline[5]) - int(dataline[4])) # extent based on annotator 2 (ELAN sets 0 if no overlap)
                elif dataline[4] == '-': # if only first annotator has event
                    dataline[7] = str(int(dataline[2]) - int(dataline[1])) # extent based on annotator 1 (ELAN sets 0 if no overlap)
                elif dataline[1] == '' and dataline[7] == '': # if line contains old overlap summary rating: keep it for presentation.
                    oldIRRlist.append(float(dataline[8]))
                elif not dataline[7].isdigit(): # if header or some other problem
                    continue # continue to next line
                if dataline[7].isdigit(): # if a (now) complete data line
                    duration.append(int(dataline[7])) # keep all (updated) extents for later use
                    overlap.append(int(dataline[6])) # keep all overlaps (in ms) for later use
            fid.close()
            try: # calculate new reliability and store for saving
                newIRRlist.append(float(sum(overlap))/float(sum(duration)))
                IRRdata[irrfile].append('\nWeighted overlap reliability:\t\t\t\t\t\t\t\t' + str(newIRRlist[-1]) + '\n')
            except:
                print("Overlap list: " + str(overlap))
                print("Duration list: " + str(duration))
                raise
    try:
        irroldvar.set('%.3f' % (float(sum(oldIRRlist))/float(len(oldIRRlist))))
        irrnewvar.set('%.3f' % (float(sum(newIRRlist))/float(len(newIRRlist))))
        irrstatvar.set("New reliability statistic calculated - Save?")
    except:
        print("old irr list: " + str(oldIRRlist))
        print("new irr list: " + str(newIRRlist))
        irrstatvar.set("Error!")
        raise
        
def validateProcessParams():
    # Checking different combinations of tiers and events selected by the user, to make sure
    #  all required information is entered.
    if FOLDERFILE == '': # no main file loaded
        tkMessageBox.showinfo(title="Message", message="At least one .eaf-file must be loaded in order to perform the analysis.")
        prednumber = 0
    elif tdd11_var.get() == tierdefault: # no first tier
        tkMessageBox.showinfo(title="Message", message="No tier selected for Predictor 1!")
        prednumber = 0
    elif tdd12_var.get() == eventdefault: # no first event
        tkMessageBox.showinfo(title="Message", message="No tier event selected for Predictor 1!")
        prednumber = 0
    elif onoff1_var.get() == onoffdefault: # no first trigger point
        tkMessageBox.showinfo(title="Message", message="No onset or offset set for Predictor 1!")
        prednumber = 0
    elif tdd3_var.get() == tierdefault: # no dependent tier
        prednumber = 0
    elif tdd4_var.get() == eventdefault: # no dependent event
        prednumber = 0
    else:
        prednumber = 1

    if prednumber == 0: # early return if not minimum requirements are met
        return
    elif tdd21_var.get() != tierdefault: # if optional predictor...
        prednumber = 2 # if check reaches this point, there is a first predictor, and likely a second predictor.
        if tdd22_var.get() == eventdefault:
            prednumber = 0
            tkMessageBox.showinfo(title="Message", message="No tier event selected for Predictor 2!")
        elif onoff2_var.get() == onoffdefault:
            prednumber = 0
            tkMessageBox.showinfo(title="Message", message="No onset or offset set for Predictor 2!")

    return prednumber

def processTCA():
    t_start = datetime.now()
    global a
    global results
    global plotbins
    global plotresults
    
#	FOLDERFILE = '/home/richard/Dropbox/pythonbox/Elan_VWP/data/HI2-HIP2strukt2.eaf' # for testing
    prednumber = validateProcessParams()
    if prednumber == 0: # if no predictors or otherwise the set parameters are invalid.
        return
    elif prednumber == 1:
        predtiers = [tdd11_var.get()]
        predevents = [tdd12_var.get()]
        predpoints = [onoff1_var.get()]
        prednames = [tdd12_var.get() + '_' + onoff1_var.get()]
    elif prednumber == 2:
        predtiers = [tdd11_var.get(), tdd21_var.get()]
        predevents = [tdd12_var.get(), tdd22_var.get()]
        predpoints = [onoff1_var.get(), onoff2_var.get()]
        prednames = [tdd12_var.get() + '_' + onoff1_var.get(), tdd22_var.get() + '_' + onoff2_var.get()]
    print("Predictors: " + str(prednumber))
    a.clear() # clear plot already here, if something breaks we don't have be confused by an old and irrelevant plot
    results = []
    plotresults = []
    dep_tier = tdd3_var.get() # dependent variable tier
    dep_event = tdd4_var.get() # dependent variable event
    winsize = int(winvar.get()) # window size in milliseconds   
    overlap_tick = 0 # for testing
    # binsize available from root
    # res available from root    
    for pn in range(prednumber): # for every predictor
        pred_tier = predtiers[pn] # using predictable StringVar names to get parameters
        pred_event = predevents[pn]
        pred_point = predpoints[pn]
        pred_name = prednames[pn]
#        print("Processing predictor: " + str(pn) + " dd1: " + pred_tier + " dd2: " + pred_event)
        # processing should happen here at this level, under the prednumber loop

        ##	# FOR TESTING!
        #	pred_tier = 'HI Task'
        #	pred_event = 'Task'
        #	pred_point = 'offset'
        #	dep_tier = 'HIP Task'
        #	dep_event = 'Task'
        #	winsize = 1000
        #	print("pred_tier is: " + pred_tier)
        #	print("pred_event is: " + pred_event)
        #	print("pred_point is: " + pred_point)
        #	print("dep_tier is: " + dep_tier)
        #	print("dep_event is: " + dep_event)
        #	print("winsize is: " + repr(winsize))

        for filename in filenames:
            print(filename)
            barename = re.findall('[ \w.]+$', filename)[0]
            timeslots = timetable(filename) # create time table of all time periods in the ELAN file (which are labelled)
            maxtime = dictTupleMax(timeslots) # latest time point
            fp = []
            fp2 = []
            fd = []
            fd2 = []
            ref_id = None
            align_id = None
            dep_events = []
            ptime = None
            e_count = 0
            overlap_checker = [] 
#            overlap_checker = nans((1,winsize/res))
#            overlap_counter = 0
            with open(filename) as x: f = x.read()
            pattern = re.compile('(?<=TIER_ID="' + re.escape(pred_tier) + '">).+?(?=</TIER>)' , re.DOTALL) # FIRST extract all tier text
            fp = re.search(pattern, f) # extract whole tier
            if fp == None: # If the selected tier does not exist for this data file
                print("Did not find predictive tier!")
                continue
    #        pattern = re.compile('.*?<ANNOTATION_VALUE>' + re.escape(pred_event) + '</ANNOTATION_VALUE>', re.DOTALL)# THEN find relevant tier events --- GREEDY PROBLEM! ---
            pattern = re.compile('<ANNOTATION>.*?</ANNOTATION>', re.DOTALL) # pattern for getting all annotations in tier
            fp = re.findall(pattern, fp.group()) # extract all events in that tier, in a list
            fp2 = []
            for e in fp: # for every annotation
                if '<ANNOTATION_VALUE>' + pred_event + '</ANNOTATION_VALUE>' in e: # now only get specific annotations
                    fp2.append(e)
            fp = fp2 # replace with only relevant (predictive) annotations
            if fp == None: # If no predictive events were found in this file
    #            print("No predictive events found!")
                continue
    #        print("Number of fp events: " + str(len(fp)))
    #        print("Event here:")
    #        for i in fp:
    #            print(i.group())
    #        print(fp[0])
            pattern = re.compile('(?<=TIER_ID="' + re.escape(dep_tier) + '">).+?(?=</TIER>)' , re.DOTALL) # FIRST extract all dep tier text
            fd = re.search(pattern, f) # extract whole dependent tier
    #            if fd != None: print("Found dependent tier: " + dep_tier)
            if fd == None:
                print("No dependent tier found!")
                continue
    #        pattern = re.compile('(?<=<ANNOTATION>).+?' + re.escape(dep_event) + '(?=</ANNOTATION_VALUE>)', re.DOTALL)# THEN find relevant tier events            
            pattern = re.compile('<ANNOTATION>.*?</ANNOTATION>', re.DOTALL) # pattern for getting all annotations in tier
            fd = re.findall(pattern, fd.group()) # extract all events in that tier, in a list
            fd2 = []
            for e in fd: # for every annotation
                if '<ANNOTATION_VALUE>' + dep_event + '</ANNOTATION_VALUE>' in e: # now only get specific annotations
                    fd2.append(e)
            fd = fd2 # replace with only relevant (dependent) annotations
    #        testwait(fd)
            if fd == None:
                print("No dependent events of the selected type found!")
                raise Exception("No proper handling of cases with no dependent events exist yet!") # should ideally return a vector of NaNs -- remains to be implemented.
            for de in fd: # for every dependent event
                align_id = re.search('ALIGNABLE_ANNOTATION ANNOTATION_ID="(\w+)"', de)
                ref_id = re.search('<REF_ANNOTATION ANNOTATION_ID="(\w+)" ANNOTATION_REF="\w+">', de)
                if align_id != None : # if its an "alignable" annotation
                    dep_events.append(timeslots[align_id.group(1)])
                elif ref_id != None : # if its a "connected" annotation
                    dep_events.append(timeslots[ref_id.group(1)])
                else:
                    raise Exception("Found event was neither alignable nor connected")
                
    
            e_count = 0
            for e in fp: # for every pred event (we will check if there is a dep event in its window)
                # I need to only match for the latest match in each event
    #            print("Event e: " + str(e))
                align_id = re.search('ALIGNABLE_ANNOTATION ANNOTATION_ID="(\w+)"', e)
                ref_id = re.search('<REF_ANNOTATION ANNOTATION_ID="(\w+)" ANNOTATION_REF="\w+">', e)
                if align_id != None : # if its an "alignable" annotation
    #                print("Match: " + align_id.group(1))
                    ptime = timeslots[align_id.group(1)]
                elif ref_id != None : # if its a "connected" annotation
    #                print("Match: " + ref_id.group(1))
                    ptime = timeslots[ref_id.group(1)]
                else:
                    raise Exception("Found event was neither alignable nor connected")
    #            print("Pred e: " + str(e))
    #            print("e time: " + str(ptime))
    #            print("Full fp: " + str(fp))
                if pred_point == 'onset':
                    ptime = ptime[0] # take first number, i.e. the start
                elif pred_point == 'offset':
                    ptime = ptime[1] # take second number, i.e. the stop
                else:
                    raise Exception("Could not find predictor time point!")
                e_count += 1 # event counter
                win1, win2 = int(round((ptime - winsize/2)/res)), int(round((ptime + winsize/2)/res)) # (two scalars) pred window boundaries
    #                print "Ptime is: " + str(ptime)
                pred_win = numpy.arange(int(round(win1)), int(math.ceil(win2))) # (vector) range in actual time points, length is number of elements in timewindow
                tempvector = numpy.zeros((1,len(pred_win) )) # initialize, length of analysis window
#                print("Tempvector initialized with " + str(tempvector.ndim) + " dimension(s)")
    #            print("Window 1: " + repr(win1))
    #            print("Window 2: " + repr(win2))
    #            print("Maxtime is: " + repr(maxtime/10))
    #            print("Pred_win: " + repr(pred_win))
    #            print("TV1: " + repr(tempvector))
                if win1 < 0: # if analysis window expands beyond beginning of recording
                    tempvector[0,0:win1] = numpy.nan
    #                print("TV2: " + repr(tempvector))
                if win2 > maxtime/res: # if analysis window expands beyond end of recording
                    tempvector[0,(pred_win>maxtime/res)] = numpy.nan
    #                print(pred_win>maxtime/10)
    #                print(len(pred_win))
    #                print(pred_win)
    #                print("TV3: " + repr(tempvector))
    #                print(len(tempvector[0]))
    #            print("Printing dependent events list:")
    #            print dep_events
                for de in dep_events: # check all dependent events
                    # Early termination check
                    if de[0]/res > win2 or de[1]/res < win1:
                        continue
#                    print("de:")
#                    dummyfunc(de)
#                    print("win1:")
#                    dummyfunc(win1)
#                    print("win2:")
#                    dummyfunc(win2)
#                    if de[0] > 
#                    print("----- New cycle -----")
    #                print("Analysis window center is: " + str(ptime/res))
    #                print("Analysis onset/offset are: " + str(win1) + " and " + str(win2))
    #                print("Dependent event onset and offset is:")
    #                testwait(de)
#                    if round(de[0]/res) not in pred_win and round(de[1]/res) not in pred_win: # if neither start nor stop is in pred_win # CANCEL THIS EARLY-TERMINATION - TOO RISKY
    ##                    print("Event NOT in predictive window")
#                        continue
    #                print("Event IS in predictive window")
    # Re-write everything into working with a long vector of dep_events (avoiding loops) - one big grab (analysis window) for every pred_event.
                    dep_win = numpy.arange(int(round(de[0]/res)), int(round(de[1]/res)+1), 1) # range in actual time points
#                    print("-----------------------------------")
#                    print("Event number: " + str(e_count))
#                    print("Dep win is: " + str(dep_win))
#                    print("Pred win is: " + str(pred_win))
#                    print("Old overlap is: " + str(overlap_checker))
                    for i in range(len(pred_win)): # for every time point (i from 0, list has actual times) in the predictive window
                        try:
                            if overlapfunc == "First come first serve" and pred_win[i] in overlap_checker: # if t for this pred_win has been used before.
                                tempvector[0][i] = numpy.nan
                                overlap_tick += 1
#                                print("Triggered overlap block: " + str(overlap_tick) )
                            else:
                                if pred_win[i] in dep_win: #if t of pred_win[i] is a time code that is in the dep_win
                                    tempvector[0][i] = 1
                                else:
                                    pass
#                                    tempvector[0][i] = 0
                            
#                                tempvector[0][i] = numpy.nan

                                
#                                print("overlap: " + "slice " + str(i) + "; time: " + str(pred_win[i]))
#                            else:
#                                print("NO overlap: " + "slice " + str(i) + "; time: " + str(pred_win[i]))                                
#                                pass
#                                print("normal: " + "slice " + str(i) + "; time: " + str(pred_win[i]))
                        except:
                            print(i)
                            print(tempvector)
                            raise
                overlap_checker.extend(pred_win) # add checked analysis slice/window to overlap checker.
                # the indent of the above line is important. Should extend across all pred windows.
#                        overlap_checker = overlap_checker[-int(winsize/res):]
#                        overlap_checker[0,overlap_counter] = pred_win[i]
#                        if overlap_counter<((winsize/res)-1):
#                            overlap_counter += 1
#                        else:
#                            overlap_counter = 0
    #                overlap_checker = overlap_checker[-(winsize/res):] # do not store more than necessary,
    #                i.e. not longer history than the size of the analysis window.
#                    print("New overlap checker: " + str(overlap_checker))
    #                print(overlap_checker)
    #                print("Resultvector for window: " + repr(tempvector))
#                results.append([barename, str(pn), pred_event, dep_event, binsize, e_count, tempvector.copy()])
                results.append([barename, pred_name, dep_event, binsize, e_count, tempvector])
        if 'tempvector' not in locals(): # if the tempvector was never created, e.g. not finding pred tier or dep tier (in any file).
            tkMessageBox.showinfo(title="Message", message="Empty vector. Selected non-existent tier/event?")
            return # return fuction without doing anything - nothing will seem to happen when the 'analyze' button is pressed.
        # Maintain unbinned data structure (it may be needed in future features)
            # results has all the data: a list with the final element a numpy array (2D)

    # Outside of predictor loop
    # Create binned results data
    plotbins = nans((len(results), math.ceil(winsize/float(binsize)))) # create empty bins based on data length and bin size
    for i in range(len(results)): # for every case line
#        print("Dimensions: " + str(results[i][-1].ndim))
#        print(results[i][-1])
        plotbins[i] = binning(results[i][-1], binsize, binfunc, res) # binning produces a 1D array.
#            print(plotbins[i])
        results[i].append(plotbins[i])
#        print(results[i][-1])
    # Now do the plotting
    # TAKE MEAN OF EACH PREDICTOR, NOT EVERYTHING
#    print("Plotbins")
    meanresult = nans((prednumber, plotbins.shape[1]))
    for i in range(len(prednames)): # for each predictor, 0 or 0,1
        idx = [] # ugly fix because bad choice of data structure
        for j in range(len(results)):
            if results[j][1] == prednames[i]: # if result (second column) concerns this prednumber
                idx.append(j)
#        if idx == []: # if not data for one predictor
#            print("No data for this predictor")
#            continue
        meanresult[i,:] = nanmean(plotbins[numpy.array(idx),:],0) # mean across rows for average curve to plot
#        meanresult[i,:] = nanmean(plotbins[plotbins[:,1]==i,:],0)
    plotResults(meanresult)
    print("done")
    t_stop = datetime.now()
    print("Time executed: " + str(t_stop-t_start) )
    

# Binning array (vector) data according to setting.
def binning(data, binsize, binfunc, res):
    '''Takes a 2d numpy array containing a single row and arranges it into bins.'''
    if data.ndim != 2:
        print("Input: " + str(data.ndim))
        raise TypeError("Function 'binning' did not receive a 2D array") # should only receive 2D arrays
    binsize = binsize/res # new binsize so binsize takes resolution into accounts (otherwise 100 * 10 = 1000 ms bins)
    # introduce check here for incompatible resolution/bin sizes? modulo == 0?
    newsize = int(math.ceil(len(data[0])/binsize))
    newdata = nans((1,newsize)) 
    for i in range(newsize):
        temp = data[0][(i*binsize):((i*binsize)+(binsize))] # store range
        newdata[0][i] = bincalc(temp.reshape(1,temp.size), binfunc) # bin data using selected method (input 2D, output 1D)
#        print("Binning produced array with number of dims: " + str(newdata[0].ndim))
    return newdata

# Generate bin value based on selected function
def bincalc(values, method): # values is a 2-dim numpy array with 1 row.
    if values.ndim != 2:
        raise TypeError("Function 'bincalc' did not receive a 2D array") # should only receive 2D arrays
    if values.size == 0:
        raise ValueError("Function 'bincalc' received an empty array")
    if method == "Mean":
        return nanmean(values,1).reshape((1,1)) # return a 2D array with the mean value, excluding NaNs.
    elif method == "Round up":
#        print(str(1 in values))
        if 1 in values: # assumes data has not been averaged already!
            return numpy.ones((1,1)) # return a single 1 in a 2D matrix
        elif 0 in values: # if no ones, but there is at least a zero.
            return numpy.zeros((1,1)) # return a single 0 in a 2D matrix
        else: # if neither zeros nor ones, then it has to be nans or some error
            return nans((1,1)) # return a single nan in a 2D matrix
    else:
        raise ValueError("Unknown bin function!")


def clearAll():
    global FOLDERFILE
    global filenames
    global IRRFOLDERFILE
    global irrfilenames
    global IRRdata
    global a
    global results
    global res, overlapfunc, binsize, binfunc
    
    if tabstate == 'tca':
        FOLDERFILE = ''
        filenames = []
        results = []
        try: # try to load personal settings -- if there are any.
            res, overlapfunc, binsize, binfunc = loadsettings("res", "overlapfunc", "binsize", "binfunc")
        except: # otherwise just use the default values.
            res = 10
            overlapfunc = "Double-dipping"
            binsize = 100
            binfunc = "Mean"
        tdd11_var.set(tierdefault)
        tdd12_var.set(eventdefault)
        onoff1_var.set(onoffdefault)
        tdd3_var.set(tierdefault)
        tdd4_var.set(eventdefault)
        tdd21_var.set(tierdefault)
        tdd22_var.set(eventdefault)
        onoff2_var.set(onoffdefault)
        tdd3_var.set(tierdefault)
        tdd4_var.set(eventdefault)
        winvar.set("1000")
        m = tierdropdown11.children['menu']
        m.delete(0, 'end') # remove all menu items
        m = tierdropdown12.children['menu']
        m.delete(0, 'end') # remove all menu items        
        m = tierdropdown3.children['menu']
        m.delete(0, 'end') # remove all menu items
        a.clear() # clear plot
        a.axis([0, 1, 0, 1]) # resets x- and y-axis
        canvas.draw() # redraws canvas        
        
    elif tabstate == 'irr':
        IRRFOLDERFILE = ''
        irrfilenames = []
        IRRdata = {}
        # resetting status field too...
        irrfilevar.set("No file/folder selected")
        irrnewvar.set("(Not computed yet)")
        irroldvar.set("(Not computed yet)")
        irrstatvar.set("Start by loading one or several files")
        
def clearPred2():
    '''Reset dropdown menus for predictor 2.'''
    tdd21_var.set(tierdefault)
    tdd22_var.set(eventdefault)
    onoff2_var.set(onoffdefault)
    tierdropdown22.children['menu'].delete(0, 'end') # remove all menu options in event menu

def saveResults():
    '''Save results of analysis.'''
    if tabstate == 'tca':
        if len(results) == 0:
            tkMessageBox.showinfo(title="Message", message="At least one .eaf-file must be loaded and analyzed in order to have results to save.")
            return
        with open('results.txt', 'w') as x:
            x.write('\t'.join(["subjectfile", "pred_event", "dep_event", "binsize", "event_num", "bin", "value"])+'\n')
            for line in results: # for every (wide) result line
                for i in xrange(0, len(line[-1])): # for every element in 1D array, assuming array is placed last, i.e. the binned data
                    templist = [unicode(line[0]), unicode(line[1]), unicode(line[2]), unicode(line[3]), unicode(line[4])]
                    templist.append(unicode(i+1))
                    if binfunc == "Round up":
                        templist.append( '{:0.0f}'.format(line[-1][i]) ) # format to string with no decimals, keep nans.
#                        templist.append(unicode(int(line[-1][i]))) # if its purely binomial output - use no decimals
                    else:
                        templist.append(unicode(line[-1][i]))
                    x.write('\t'.join(templist)+'\n')
        tkMessageBox.showinfo(title="Message", message="Results were saved in file: results.txt")
    elif tabstate == 'irr':
        for key in IRRdata: # taking information from global IRRdata
            path, fname, extension = splitPath(key)
            fid = open(path + fname + '_corrected.' + extension, 'w')
            for line in IRRdata[key]:
                fid.write(line)
            fid.close()
        irrstatvar.set("All done!")
        tkMessageBox.showinfo(title="Message", message='''Results were saved in the same folder with the suffix "_corrected" added to them.''')
    
def plotResults(plotresults):
    '''Plots results. Input is numpy array with one predictor per row (max 2)'''
    global a
#    if plotresults == []
    a.clear() # important to not plot overlaid
    a.plot(numpy.transpose(plotresults)) # plot results over time
    wz = int(winvar.get()) # get analysis window size
    majorloc = plt.MultipleLocator(int(round(wz/(4*binsize)))) # where to place ticks
    wzl = range(0,int(wz*1.2), wz/4)
    wzl2 = []
    for w in wzl:
        wzl2.append(w-(int(wz/2))) # centering ticks (assuming symmetric analysis window)
    majorformat = plt.FixedFormatter(wzl2) # plot using our month counter
    a.xaxis.set_major_locator(majorloc) # adjust axis according to above
    a.xaxis.set_major_formatter(majorformat) # adjust axis according to above
    if min(plotresults.shape) > 1: # if more than one data plot # BAD CHECK - COULD BE WRITTEN BETTER
        a.legend(('Predictor 1', 'Predictor 2'), prop={'size':10}) # place a legend
    else:
        pass # otherwise we don't need a legend
    canvas.draw()

def settingsDialog():
    global setroot
    global res
    global overlapfunc
    global binsize
    global binfunc
    global resvar
    global overlap_var
    global binvar
    global binfunc_var
    setroot = tk.Tk()
    w, h = 400, 200 # Size of root window
    setroot.geometry("%dx%d+200+150" % (w, h)) # set root geometry
    setroot.title('ETC settings')
    hpad = 10
    menuwidth = 20
    # Resolution
    reslabel = tk.Label(setroot, text="Resolution (ms):", width=20, anchor="w") # anchor="w"
    reslabel.grid(row=0, column=0, sticky="w", padx=hpad)
    resvar = tk.StringVar(setroot)
    resvar.set(str(res))
    resentry = tk.Entry(setroot, textvariable=resvar, width=12)
    resentry.grid(row=0, column=1, padx=hpad, sticky="w")
    # Overlap handling
    overlaplabel = tk.Label(setroot, text="Overlap handling:", width=20, anchor="w") # anchor="w"
    overlaplabel.grid(row=1, column=0, sticky="w", padx=hpad)
    overlap_options = ("First come first serve", "Double-dipping")
    overlap_var = tk.StringVar(setroot)
    overlap_var.set(overlapfunc)
    overlap_menu = tk.OptionMenu(setroot, overlap_var, *overlap_options)
    overlap_menu.grid(row=1, column=1, sticky="w", padx=hpad)
    # Bin size
    binlabel = tk.Label(setroot, text="Bin size (ms):", width=20, anchor="w") # anchor="w"
    binlabel.grid(row=2, column=0, sticky="w", padx=hpad)
    binvar = tk.StringVar(setroot)
    binvar.set(str(binsize))
    binentry = tk.Entry(setroot, textvariable=binvar, width=12)
    binentry.grid(row=2, column=1, padx=hpad, sticky="w")
    # Bin function
    binfunclabel = tk.Label(setroot, text="Bin function:", width=20, anchor="w") # anchor="w"
    binfunclabel.grid(row=3, column=0, sticky="w", padx=hpad)
    binfunc_options = ("Mean", "Round up")
    binfunc_var = tk.StringVar(setroot)
    binfunc_var.set(binfunc)
    binfunc_menu = tk.OptionMenu(setroot, binfunc_var, *binfunc_options)
    binfunc_menu.grid(row=3, column=1, sticky="w", padx=hpad)
    # Divider
    setcanvas = tk.Canvas(setroot, width = 400, height = 20, highlightthickness = 0)
    setcanvas.grid(row=5, column=0, columnspan=3, padx=0, sticky="w")
    setcanvas.create_line(10, 10, 390, 10, width = 1.0, fill="grey")
    # OK/Cancel part
    okbutton = tk.Button(setroot, text='OK', command=okclosesettings, anchor="w")
    okbutton.grid(row=6, column=0, sticky="w", padx=hpad)
    closebutton = tk.Button(setroot, text='Cancel', command=setroot.destroy, anchor="w") #command=lambda setroot=setroot:quit(setroot)
    closebutton.grid(row=6, column=1, sticky="w", padx=hpad)

# Updating settings and closing settings window
def okclosesettings():
#    global setroot # apparently not needed to destroy window.
    global res
    global overlapfunc    #irrframe.grid_forget()
    #graphframe.grid()
    global binsize
    global binfunc
    res = int(resvar.get()) # getting from root space
    overlapfunc = overlap_var.get() # getting from root space
    binsize = int(binvar.get()) # getting from root space
    binfunc = binfunc_var.get() # getting from root space
    setroot.destroy() # getting from root space

# Closing main program and saving settings
def quitsave():
    global winsize
    winsize = int(winvar.get())
    # save settings for next loading of program
    with open('ETC_settings.ini', 'w') as x:
        for var in ["res", "overlapfunc", "binsize", "binfunc", "winsize"]:
            x.write(var + ':' + str(eval(var)) + '\n') # write variable name and variable contents
    quit(root)
    
def setTCtab():
    '''Setting time-course tab as active tab'''
    global tabstate
    tab1.configure(bg=col_act)
    tab2.configure(bg=col_inact)    
    tabstate = 'tca'
    irrframe.lower()
    graphframe.lift()

def setIRRtab():
    '''Setting IRR tab as the active tab'''
    global tabstate
    tab2.configure(bg=col_act)
    tab1.configure(bg=col_inact)    
    tabstate = 'irr'
    graphframe.lower()
    irrframe.lift()
    
def allwidgets_recursive(widget):
    '''Gathers widget handles of widget and all its children in one list'''
    widlist = widget.winfo_children()
    for wid in widlist:
        if wid.winfo_children():
            widlist.extend(wid.winfo_children())
    return widlist
    
def testingParams():
    global FOLDERFILE, filenames
    if os.name == 'posix':
        FOLDERFILE = '/home/richard/Dropbox/pythonbox/Elan_VWP/data files/HI2-HIP2strukt1.eaf'
        filenames = [FOLDERFILE]
    else:
        pass
    tdd11_var.set('%spa@HIX')
    tdd12_var.set('$SPEC:CONFNEW:conf:y')
    tdd21_var.set('%spa@HIX')
    tdd22_var.set('$SPEC:CONFNEW:conf:y')
    tdd3_var.set('HI Face')
    tdd4_var.set('Face')
    onoff1_var.set('onset')
    onoff2_var.set('offset')


# GLOBALS AND DEFAULTS
try: # try to load personal settings -- if there are any.
    res, overlapfunc, binsize, binfunc, winsize = loadsettings("res", "overlapfunc", "binsize", "binfunc", "winsize")
except: # otherwise just use the default values.
    print("Loading settings threw an exception...")
    raise

#print "Resolution is " + res
#print "Overlapfunc is " + overlapfunc
#print "Bin size is " + binsize
#print "Bin function is " + binfunc

###############################
####  GRAPHICAL INTERFACE  ####
FOLDERFILE = ''
filenames = []
root = tk.Tk()
img = tk.PhotoImage(file='icon.gif', width=256, height=256) # create icon object from file
root.tk.call('wm', 'iconphoto', root._w, img) # call tk wm to change icon
w, h = 800, 650 # Size of root window
if os.name == 'nt': # manually set height for Windows
    h += 90
root.geometry("%dx%d+0+0" % (w, h)) # set root geometry
root.title('ELAN analysis companion ' + myversion)
hpad = 10
menuwidth = 20
col_act = '#ededed'
col_inact = '#d4d4d4'

# default Tkinter color is #d9d9d9


### TAB FRAME ###
tabframe = tk.Frame(master=root, borderwidth=0) #, width=800, height=30)
tabframe.grid(row=0, columnspan=4, sticky='nsew')#
tab1 = tk.Button(master=tabframe, text='Timecourse analysis',relief="flat",\
    highlightthickness=0, bg=col_act, state='normal', command=setTCtab)
tab1.grid(row=0, column=0)
tab2 = tk.Button(master=tabframe, text='Inter-rater reliability', relief="flat",\
    highlightthickness=0, bg=col_inact, state='normal', command=setIRRtab)
tab2.grid(row=0, column=1)

#### INTERRATER RELIABILITY FRAME ####
# Frame
irrframe = tk.Frame(master=root, borderwidth=0, relief="flat", width=800, height=300, bg=col_act)
irrframe.grid(row=1, column=0, columnspan=4, rowspan=2, sticky='nwes')

# Status pre-text
irrprelabel1 = tk.Label(irrframe, text="Status: ", width=15, anchor="w") # anchor="w"
irrprelabel1.grid(row=0, column=0, padx=hpad, sticky="we")
# Status text
irrstatvar = tk.StringVar(irrframe)
irrstatvar.set("Start by loading one or several files")
irrstatentry = tk.Label(irrframe, textvariable=irrstatvar, width=40, anchor="w")
irrstatentry.grid(row=0, column=1, padx=hpad, sticky="we") # sticky w

# Folder pre-text
irrprelabel2 = tk.Label(irrframe, text="File/Folder: ", width=15, anchor="w") # anchor="w"
irrprelabel2.grid(row=1, column=0, padx=hpad, sticky="w")
# Folder result text
irrfilevar = tk.StringVar(irrframe)
irrfilevar.set("No file/folder selected")
irrfileentry = tk.Label(irrframe, textvariable=irrfilevar, width=60, anchor="w")
irrfileentry.grid(row=1, column=1, padx=hpad, sticky="w") # sticky w

# Result pre-text
irrprelabel3 = tk.Label(irrframe, text="Results... ", width=15, anchor="w") # anchor="w"
irrprelabel3.grid(row=2, column=0, padx=hpad, sticky="we")
# Old result pre-text
irrprelabel4 = tk.Label(irrframe, text="     Old average reliability: ", width=25, anchor="w") # anchor="w"
irrprelabel4.grid(row=3, column=0, padx=hpad, sticky="we")
# New result pre-text
irrprelabel5 = tk.Label(irrframe, text="     New average reliability: ", width=25, anchor="w") # anchor="w"
irrprelabel5.grid(row=4, column=0, padx=hpad, sticky="we")
# Old result calculation
irroldvar = tk.StringVar(irrframe)
irroldvar.set("(Not computed yet)")
irroldlabel = tk.Label(irrframe, textvariable=irroldvar, width=40, anchor="w")
irroldlabel.grid(row=3, column=1, padx=hpad, sticky="we") # sticky w
# New result calculation
irrnewvar = tk.StringVar(irrframe)
irrnewvar.set("(Not computed yet)")
irrnewlabel = tk.Label(irrframe, textvariable=irrnewvar, width=40, anchor="w")
irrnewlabel.grid(row=4, column=1, padx=hpad, sticky="we") # sticky w





### GRAPH FRAME ###
f = Figure(figsize=(8,3), dpi=98, facecolor=col_act) # matplotlib object
a = f.add_subplot(1,1,1)
#f.SubplotParams.update(left=0, right=0, bottom=0, top=0, wspace=0, hspace=0)
graphframe = tk.Frame(master=root, borderwidth=0, relief="flat", width=w, height=300)
graphframe.grid(row=1, columnspan=4, column=0, sticky="nwes")
canvas = FigureCanvasTkAgg(f, master=graphframe)
canvas.get_tk_widget().grid() # (sticky='nwes')
canvas.get_tk_widget().configure(borderwidth=0)
canvas.show()

### OPTIONS FRAME ###
TCoptionframe = tk.Frame(master=root, borderwidth=0, relief="flat", width=w, \
    height=250, bg=col_act)
TCoptionframe.grid(row=2, column=0, columnspan=4, sticky="we")#

### LEFT PANEL 1 ###
# Left option panel - label
pred1label = tk.Label(TCoptionframe, text="Predictor 1:", width=20, anchor="w") # anchor="w"
pred1label.grid(row=0, column=0, sticky="w", padx=hpad)

# Left option panel - Tier drop-down
tdd11_options = [tierdefault, "dummy value"]
tdd11_var = tk.StringVar(TCoptionframe, name="tdd11_var")
tdd11_var.set(tierdefault)
tierdropdown11 = tk.OptionMenu(TCoptionframe, tdd11_var, *tdd11_options)
tierdropdown11.grid(row=1, column=0, sticky="we", padx=hpad)
m = tierdropdown11.children['menu']
m.delete(0,'end') # remove init option

# Left option panel - Event drop-down
tdd12_options = ["event1", "event2", "event3"]
tdd12_var = tk.StringVar(TCoptionframe, name="tdd12_var")
tdd12_var.set(eventdefault)
tierdropdown12 = tk.OptionMenu(TCoptionframe, tdd12_var, *tdd12_options)
tierdropdown12.grid(row=2, column=0, sticky="we", padx=hpad)
m = tierdropdown12.children['menu']
m.delete(0,'end') # remove init option

# Left option panel - onset/offset menu
onoff1_options = ["onset", "offset"]
onoff1_var = tk.StringVar(TCoptionframe)
onoff1_var.set(onoffdefault)
onoffdropdown1 = tk.OptionMenu(TCoptionframe, onoff1_var, *onoff1_options)
onoffdropdown1.grid(row=3, column=0, sticky="we", padx=hpad)

### LEFT PANEL 2 ###
# Dummy space
dummylabel2 = tk.Label(TCoptionframe, text="", width=20, anchor="w")
dummylabel2.grid(row=4, column=0, sticky="w", padx=hpad)

# Left option panel - label
pred2label = tk.Label(TCoptionframe, text="Predictor 2:", width=20, anchor="w") # anchor="w"
pred2label.grid(row=5, column=0, sticky="w", padx=hpad)

# Left option panel - Tier drop-down
tdd21_options = [tierdefault]
tdd21_var = tk.StringVar(TCoptionframe, name="tdd21_var") # name required by prepdropdown function
tdd21_var.set(tierdefault)
tierdropdown21 = tk.OptionMenu(TCoptionframe, tdd21_var, *tdd12_options)
tierdropdown21.grid(row=6, column=0, sticky="we", padx=hpad)
m = tierdropdown21.children['menu']
m.delete(0,'end') # remove init option

# Left option panel - Event drop-down
tdd22_options = ["event1", "event2", "event3"]
tdd22_var = tk.StringVar(TCoptionframe, name="tdd22_var") # name required by prepdropdown function
tdd22_var.set(eventdefault)
tierdropdown22 = tk.OptionMenu(TCoptionframe, tdd22_var, *tdd22_options)
tierdropdown22.grid(row=7, column=0, sticky="we", padx=hpad)
m = tierdropdown22.children['menu']
m.delete(0,'end') # remove init option

# Left option panel - onset/offset menu
onoff2_options = ["onset", "offset"]
onoff2_var = tk.StringVar(TCoptionframe)
onoff2_var.set(onoffdefault)
onoffdropdown2 = tk.OptionMenu(TCoptionframe, onoff2_var, *onoff2_options)
onoffdropdown2.grid(row=8, column=0, sticky="we", padx=hpad)

# Clear button for Predictor 2
clearPred2button = tk.Button(TCoptionframe, text='Clear predictor', command=clearPred2)
clearPred2button.grid(row=8, column=1, sticky="we", padx=hpad)

### MIDDLE PANEL ###
# Middle option panel - label
deplabel = tk.Label(TCoptionframe, text="Dependent variable:", width=20, anchor="w") # anchor="w"
deplabel.grid(row=0, column=1, sticky="w", padx=hpad) #sticky="w"

# Middle option panel - Tier drop-down
tdd3_var = tk.StringVar(TCoptionframe, name="tdd3_var")
tdd3_var.set(tierdefault)
tierdropdown3 = tk.OptionMenu(TCoptionframe, tdd3_var, *tdd11_options)
tierdropdown3.grid(row=1, column=1, sticky="we", padx=hpad)
m = tierdropdown3.children['menu']
m.delete(0,'end') # remove init option

# Middle option panel - Event drop-down
tdd4_options = ["event1", "event2", "event3"]
tdd4_var = tk.StringVar(TCoptionframe, name="tdd4_var")
tdd4_var.set(eventdefault)
tierdropdown4 = tk.OptionMenu(TCoptionframe, tdd4_var, *tdd4_options)
tierdropdown4.grid(row=2, column=1, sticky="we", padx=hpad)
m = tierdropdown4.children['menu']
m.delete(0,'end') # remove init option

### RIGHT PANEL ###
# Right option panel - window label
winlabel = tk.Label(TCoptionframe, text="Window size (ms): ", width=15, anchor="w") # anchor="w"
winlabel.grid(row=1, column=2, padx=hpad, sticky="w")

# Right option panel - window entry
winvar = tk.StringVar(TCoptionframe)
winvar.set(str(winsize))
winentry = tk.Entry(TCoptionframe, textvariable=winvar, width=12)
winentry.grid(row=1, column=3, padx=hpad, sticky="w") # sticky w

# Right - settings
settingsbutton = tk.Button(TCoptionframe, text='Settings', command=settingsDialog)
settingsbutton.grid(row=2, column=3, sticky="we", padx=hpad)

### DIVIDER BAR
# divider bar
barcanvas = tk.Canvas(root, width = w, height = 20, highlightthickness = 0, bg=col_act)
barcanvas.grid(row=3, column=0, columnspan=4, padx=0, sticky="w")
barcanvas.create_line(10, 10, w-10, 10, width = 1.0, fill="grey")

### BOTTOM I/O PANEL
# Left - load-frame
loadframe = tk.Frame(root, bg=col_act)
loadframe.grid(row=4, column=0, columnspan=4, sticky="we")

# Left - load button
loadbutton = tk.Button(loadframe, text='Load file(s)', command=loadButtonFunc, anchor="w")
loadbutton.grid(row=0, column=0, sticky="we", padx=hpad)

# Left - recursion label
recurlabel = tk.Label(loadframe, text="Load all files in selected folder?", width=30)
recurlabel.grid(row=0, column=1, sticky="we")

# Left - recursion button
tickvar = tk.IntVar()
tickbox1 = tk.Checkbutton(loadframe, variable=tickvar, command = loadFolder) # reloads data upon check/uncheck
tickbox1.grid(row=0, column=3, sticky="w")

# Left - analyze button
analyzebutton = tk.Button(loadframe, text='Analyze!', command=analyzeFiles)
analyzebutton.grid(row=1, column=0, sticky="we", padx=hpad)

# Left - save button
savebutton = tk.Button(loadframe, text='Save results', command=saveResults)
savebutton.grid(row=2, column=0, sticky="we", padx=hpad)

# Right - clear button
clearbutton = tk.Button(loadframe, text='Clear all', command=clearAll)
clearbutton.grid(row=1, column=3, sticky="we", padx=hpad)

# Right - quit button
quitbutton = tk.Button(loadframe, text='Quit', command=quitsave) # anchor="w") # anchor is only for text inside the widget
quitbutton.grid(row=2, column=3, sticky="we", padx=hpad)

# Main loop
root.grid()
#loadbutton.focus()

# Fixing colors cross-platform style:
widgetlist = allwidgets_recursive(root)
for wid in widgetlist:
    wid.configure(bg=col_act)
    try:
        wid.configure(highlightthickness=0)
    except:
        pass
# Manual touch-ups:
tabframe.configure(background=col_inact)
tab2.configure(bg=col_inact)
winentry.configure(bg='#ffffff')
root.configure(background=col_act)

#dummyfunc()
#testingParams() # for testing purposes
#processTCA()

root.mainloop() # initiate main loop
			
