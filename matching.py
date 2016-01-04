#!/usr/bin/env python -O
# Copyright (c) 2016 Allison Sliter
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the 'Software'), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
# The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
# THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
import sys
import datetime as dt
import argparse
import itertools
from collections import defaultdict
import csv

"""
These functions modified and ported from C code by Brian Roark. 
"""
class PatternPreprocessor:
    #######################
    # Pre-processing utility functions
    #######################

    def __init__(self, patt):
        self.pattern = patt
        self.arr_len = len(patt) + 1 # length to use for vectors
        self.Z = [0] * self.arr_len # Gusfield Z-values
        self.sp = [0] * self.arr_len # KMP sp' suffix length values
        self.F = [0] * self.arr_len # KMP failure function values
        self.badc = self.get_bad_char(self.pattern) # weak bad character values for Boyer-Moore
        self.L_prime = [0] * self.arr_len # strong "L" values for Boyer-Moore (L'), Gusfield theorem 2.2.2, p. 21
        self.l_prime = [0] * self.arr_len # l-values for Boyer-Moore - Gusfield theorem 2.2.4, p. 21
        
        self.bc2 = self.get_bad_2char(self.pattern)

        self.calc_good_suffix()        
        self.Z, self.sp, self.F = self.calc_z_vals_and_failure_func(self.pattern)
        

    """
    Utility function for getting the longest matching prefix of two string/offsets
    """
    def matchlen(self, s1, pos1, s2, pos2):
        to_ret = 0
        l1 = len(s1)
        l2 = len(s2)
    
        idx1 = pos1
        idx2 = pos2
    
        while idx1 < l1 and idx2 < l2 and s1[idx1] == s2[idx2]:
            to_ret += 1
            idx1 += 1
            idx2 += 1
        
        return to_ret
    
    """
    Function to compute Z values, failure function values, and sp' suffix values

    Modified from C code by Brian Roark; as a result, it's not particularly Pythonic. :-/
    
    """
    def calc_z_vals_and_failure_func(self, str_to_use):
        r = 0
        l = 0
        updater_l = False
        patt_len = len(str_to_use)
        vec_len_to_use = patt_len + 1
        
        Z_to_ret = [0] * vec_len_to_use
        sp_to_ret = [0] * vec_len_to_use
        F_to_ret = [0] * vec_len_to_use
        
        i_counter = 0 # just to keep track of 
        for i in range(patt_len):
            i_counter = i
            F_to_ret[i] = sp_to_ret[i - 1]
            upater_l = False # reset if needed from prev. iteration
            if i > r: # outside of a z-box
                Z_to_ret[i] = self.matchlen(str_to_use, i, str_to_use, 0)
                if Z_to_ret[i] > 0:
                    updater_l = True
            else: # inside a z-box
                if Z_to_ret[i - l] < r - i + 1:
                    Z_to_ret[i] = Z_to_ret[i - l]
                else:
                    Z_to_ret[i] = r - i + 1;
                    Z_to_ret[i] += self.matchlen(str_to_use, r + 1, str_to_use, r - i + 2)
                    updater_l = True
            
            if updater_l:
                r = i + Z_to_ret[i] - 1
                l = i
                if sp_to_ret[r] == 0:
                    sp_to_ret[r] = Z_to_ret[i]
        F_to_ret[-1] = sp_to_ret[-2] # clean up
        
        return (Z_to_ret, sp_to_ret, F_to_ret)
        
    
    
    """
    Calculate Boyer-Moore "Good Suffix" rule
    """

    def calc_good_suffix(self):
        patt_len = self.arr_len - 1 # the actual pattern length
        k = 0
        last = 0

        reversed_pattern = self.pattern[::-1]
        rev_z, rev_sp, rev_f = self.calc_z_vals_and_failure_func(reversed_pattern)
        
        # compute L'
        for i in range(1, patt_len - 1): # set strong good suffix values L' from the reversed version of the pattern
            k = patt_len - rev_z[patt_len - i - 1];
            self.L_prime[k] = i
        last = 0
        
        # now commpute l', also using the Z-values of the reversed pattern
        for i in range(patt_len - 1, -1, -1): # go all the way down to zero
            k = patt_len - i - 1
            if rev_z[patt_len - k - 1] == k + 1:
                self.l_prime[i] = k + 1
                last = k + 1
            else:
                self.l_prime[i] = last


    """
    Computes the values needed for the weak "Bad Character" rule for Boyer-Moore

    From Gusfield section 2.2.2: For each character x in the alphabet, let R(x) be the position of right-most occurrence of character x in P. R(x) is defined to be zero if x does not occur in P.

    """
    def get_bad_char(self, patt):
        bc = defaultdict(int)    
        for idx, c in enumerate(patt):
            bc[c] = idx
        return bc
    
    def get_bad_2char(self, patt):
        bc = defaultdict(int)
        for i in range(0,len(patt)-1):
            x = patt[i]
            y = patt[i + 1]
            xy = x+y
            bc[xy] = i+1
            
        
        return bc
    

#######################
# Matching algorithms
#######################

"""
implements the naive quadratic-time exact matching algorithm
arguments: 
    patt: the pattern ("needle") to search for
    preproc: a precomputed instance of the PatternPreprocessor class for patt, NOT USED for the naive search
    txt: the text in which to search for patt (the "haystack")
returns: a list containing the offsets in txt at which occurrences of patt were found
"""
def naive_match(patt, preproc, txt):
    matches = [] # will store the indices of matches

    patt_len = len(patt) # save these ahead of time, since we'll be using them a lot
    txt_len = len(txt)
    last = txt_len - patt_len + 1 # the last position in txt at which patt could occurr

    # setup variables for loops
    p_idx = -1 # offset within the pattern for a current possible match
    t_idx = -1 # our offset within txt for the current possible match
    outer_t_idx = -1 # our offset within txt for the outer loop (how far are we in the string?)
    
    # listify for faster indexing - grr, Python...
    t_chars = list(txt) #array(list(txt))
    p_chars = list(patt) #array(list(patt))
    
    # move one character at a time through our string...
    while outer_t_idx < last:
        outer_t_idx += 1
        t_idx = outer_t_idx
        p_idx = 0
        # try to start a new match at outer_t_idx; continue until we run out of pattern, text, or until we stop seeing a match
        while p_idx < patt_len and t_idx < txt_len and p_chars[p_idx] == t_chars[t_idx]:
            t_idx += 1
            p_idx += 1
        if p_idx >= patt_len: # we must have gotten all the way through the pattern- i.e., the previous loop must have terminated because p_idx was > patt_len, not because the match ended, etc.
            matches.append(outer_t_idx) 
    return matches
    
"""
implements the Knuth-Morris-Pratt matching algorithm
arguments: 
    patt: the pattern ("needle") to search for
    preproc: a precomputed instance of the PatternPreprocessor class for patt
    txt: the text in which to search for patt (the "haystack")
returns: a list containing the offsets in txt at which occurrences of patt were found
"""
def knuth_morris_pratt(patt, preproc, txt):
    matchlist = list() #where to add new matches

    p = 0 #patt alignment pointer
    t = 0 #txt pointer
    c = t #comparison pointer
    
    while (t <= len(txt)-len(patt)):
        while(p < len(patt) and patt[p] == txt[c]):
            p +=1
            c +=1
            
        if (p >= len(patt)):
            matchlist.append(t)
            
        
        t += max(1, preproc.F[p]*(p-1))
  
        
        c = t
        p = preproc.F[p]
    return matchlist 

"""
implements the Boyer-Moore matching algorithm
arguments: 
    patt: the pattern ("needle") to search for
    preproc: a precomputed instance of the PatternPreprocessor class for patt
    txt: the text in which to search for patt (the "haystack")
returns: a list containing the offsets in txt at which occurrences of patt were found
"""
def boyer_moore(patt, preproc, txt):
    matchlist = list()
        
    p = len(patt)-1
    t = 0
    c = t+len(patt)-1
    
    x = txt[c]
    bad_off = preproc.badc[x]
    good_off = preproc.L_prime[p]
    
    
    
    while(t+len(patt) < len(txt)):
        while(c < len(txt) and p>=0 and patt[p] == txt[c]):
            p -= 1
            c -= 1
#            if (p > 0):
#                good_off = preproc.L_prime[p-1]
            x = txt[c]
            bad_off = preproc.badc[x]

                

            
        if(p < 0):
            matchlist.append(t)
            p = 0
        if bad_off == 0:
            t = max((t + 1), c)
        else:
            t += max(1, good_off, p-bad_off)
            

        c = t + len(patt)-1
        p = len(patt)-1
        
        good_off = preproc.L_prime[p-1]
        if (c < len(txt)):
            x = txt[c]
            bad_off = preproc.badc[x]
    return matchlist 


"""
implements the Zhu - Takoaka algoritm
arguments: 
    patt: the pattern ("needle") to search for
    preproc: a precomputed instance of the PatternPreprocessor class for patt
    txt: the text in which to search for patt (the "haystack")
returns: a list containing the offsets in txt at which occurrences of patt were found
"""

def zhu_takoaka(patt, preproc, txt):
    matchlist = list()
    
    p = len(patt)-1
    t = 0
    c = t+len(patt)-1
    
    x = txt[c]
    y = txt[c+1]
    bad_off = preproc.bc2[x+y]
    good_off = preproc.L_prime[p-1]
    
    
    
    
    while(t+len(patt) <= len(txt)):
                
            
        while(p >= 0 and patt[p] == txt[c]):
            
            p -= 1
            c -= 1
            x = txt[c]
            y = txt[c+1]
            bad_off = preproc.bc2[x+y]
            if(p >= 0):
                good_off = preproc.L_prime[p-1]
            else:
                good_off = 0

            
        if(p < 0):
            matchlist.append(t)
        if bad_off == 0:
            t = max(t+1, c+1)
        else:
            t += max(1, p-bad_off, good_off)            
            

        c = t + len(patt)-1
        p = len(patt)-1
        good_off = preproc.L_prime[p-1]
        if (c+1 < len(txt)):
            x = txt[c]
            y = txt[c+1]
            bad_off = preproc.bc2[x+y]        

    return matchlist

#######################
# I/O and main program logic
#######################

parser = argparse.ArgumentParser()
parser.add_argument("patt_fname", help="a text file containing patterns to search for, one pattern per line")
parser.add_argument("text_fname", help="the text file in which to search")
args = parser.parse_args()

patterns_fname = args.patt_fname
in_fname = args.text_fname

needles = [l.strip() for l in open(patterns_fname).readlines()]

haystack = open(in_fname).read() # the text to saerch

f = open("results.csv", 'wt')
row = csv.writer(f)
row.writerow(("", "preprocestime", "naive_match", "knuth_morris_pratt"," boyer_moore", "zhu_takoaka"))

for p in needles:
    print p
    start_preproc_time = dt.datetime.now()
    pre_processed_vals = PatternPreprocessor(p) # see definition above; can ask it for things like Z-values, etc.
    end_preproc_time = dt.datetime.now()
    elapsed_preproc_time = end_preproc_time - start_preproc_time
    print "\tPre-processing time:",elapsed_preproc_time.total_seconds(),"seconds."
    time = [p, str(elapsed_preproc_time.total_seconds())]
    
    for search_algorithm in [naive_match, knuth_morris_pratt, boyer_moore, zhu_takoaka]:
        start_time = dt.datetime.now()
        matches = search_algorithm(p, pre_processed_vals, haystack)
        end_time = dt.datetime.now()
        elapsed = (end_time - start_time)
        time.append(str(elapsed.total_seconds()))
        print "\t", search_algorithm.__name__, "\t", elapsed.total_seconds(), "seconds\t", len(matches), "matches"
        
    row.writerow((time))

f.close()    
            
    
    
