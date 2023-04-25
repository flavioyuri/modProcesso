#pip install git+https://github.com/daviromero/teocomp.git -q
#pip install git+https://github.com/daviromero/automaton2bpmn.git -q
#pip install wget -q
from teocomp.dfa import DFA
from teocomp.nfa import NFA
from teocomp.nfa_e import NFA_E
from teocomp.nfa_bb import NFA_BB
#from google.colab import files
from automaton2bpmn.to_automaton import to_nfa_minimum_path
from automaton2bpmn.to_automaton import to_nfa_minimum_path_join_traces
from automaton2bpmn.to_automaton import to_nfa
from automaton2bpmn.to_automaton import get_most_frequent_traces, get_trace_frequency
from automaton2bpmn.to_automaton import removeAllSequencesOfRepetitions
from automaton2bpmn.to_bpmn import dfa_to_bpmn
from automaton2bpmn.to_bpmn import nfa_to_bpmn
from pm4py.algo.conformance.alignments.petri_net import algorithm as alignments
from pm4py.algo.evaluation.replay_fitness import algorithm as replay_fitness
from pm4py.objects.conversion.wf_net.variants import to_bpmn
from pm4py.algo.discovery.inductive import algorithm as inductive_miner    
from pm4py.visualization.bpmn import visualizer as bpmn_visualizer
from pm4py.visualization.process_tree import visualizer as pt_visualizer
from pm4py.objects.conversion.process_tree import converter as pt_converter
import wget
import os.path
import io
import pandas as pd
import unittest
from IPython.display import display, Markdown
#pip install pm4py 
import pm4py
import networkx as nx
import pandas as pd
import pylab
from pm4py.objects.log.util import dataframe_utils
from pm4py.objects.conversion.log import converter as log_converter
from pm4py.visualization.bpmn import visualizer as bpmn_visualizer
from pm4py.objects.conversion.wf_net import converter as wf_converter
import csv
from os import write
from pm4py.objects.log.importer.xes import importer as xes_importer
from pm4py.objects.conversion.log import converter as xes_converter
from pm4py.objects.conversion.wf_net.variants import to_bpmn
from pm4py.algo.discovery.inductive import algorithm as inductive_miner    
from pm4py.visualization.bpmn import visualizer as bpmn_visualizer
from pm4py.visualization.process_tree import visualizer as pt_visualizer
from pm4py.objects.conversion.process_tree import converter as pt_converter
import ipywidgets as widgets
import matplotlib.pyplot as plt

### Funções em comum


######Funções necessárias para encontrar subprocessos

class NFA_BB_Filha(NFA_BB):
  def propTransicoes(estados, transicoes):
    saidas = {}
    chegadas = {}

    for s in estados:
      saidas[s] = []
      chegadas[s] = []

    for transicao in transicoes:
      for destino in transicoes.setdefault(transicao):
        saidas[transicao[0]].append((transicao[1], destino))
        chegadas[destino].append(transicao)
      

    umaSaida = []
    destinoVarios = []

    for s in estados:
      if len(saidas[s]) <= 1 and len(chegadas[s]) <= 1:
        umaSaida.append(s)
      elif len(chegadas[s]) > 1:
        destinoVarios.append(s)
    return saidas, chegadas, umaSaida, destinoVarios#, alcanca

  def __init__(self, Q={}, Sigma={}, q0=None, delta={}, F=set(), NFAs={}, input_jff=None,keep_traces=True):
    super().__init__(Q, Sigma, q0, delta, F, NFAs, input_jff, keep_traces)
    self.saidas, self.chegadas, self.umaSaida, self.destinoVarios = NFA_BB_Filha.propTransicoes(Q, delta)
  
  



from pm4py.objects.bpmn.obj import BPMN

def buildSubProcess(nfa, subprocessNFA, bpmn, father_process, remove_unnecessary_gateways, i):
  subprocessNFA.set_epsilon_closure()
  start_event = BPMN.StartEvent(name="i_"+str(i), isInterrupting=True)
  bpmn.add_node(start_event)
  gateways = {}
  subprocess = {}
  subPro = {}
  end_events = {}
  gateways_in = {}
  gateways_out = {}
  flows = {}
  #Each state will be an exclusive gateway except those who are representing subprocesses
  for s in subprocessNFA.states:
    if s in subprocessNFA.NFAs.keys() and s not in subprocess.keys():
      subprocess[s] = BPMN.SubProcess(id=s, name=s)
      subprocess[s].set_process(father_process)
    elif s not in subprocessNFA.NFAs.keys():  
      gateways[s] = BPMN.ExclusiveGateway(id=s, name=s)
      gateways[s].set_process(father_process)
    if remove_unnecessary_gateways:
      gateways_in[s] = []
      gateways_out[s] = []

  #Adds the epsilon closure flows
  for s in subprocessNFA.states:
    for s_aux in subprocessNFA.epsilon_closure[s]:
      if s!=s_aux and s in gateways and s_aux in gateways:
        flow = BPMN.SequenceFlow(gateways[s], gateways[s_aux])
        bpmn.add_flow(flow)
        if remove_unnecessary_gateways:
          gateways_in[gateways[s_aux]].append(gateways[s])
          gateways_out[gateways[s]].append(gateways[s_aux])
          flows[gateways[s], gateways[s_aux]] = flow
      elif s!=s_aux and s in subprocess and s_aux in gateways:
        flow = BPMN.SequenceFlow(subprocess[s], gateways[s_aux])
        bpmn.add_flow(flow)    
        if remove_unnecessary_gateways:
          gateways_in[gateways[s_aux]].append(subprocess[s])
          gateways_out[subprocess[s]].append(gateways[s_aux])
          flows[subprocess[s], gateways[s_aux]] = flow
      elif s!=s_aux and s in gateways and s_aux in subprocess:
        flow = BPMN.SequenceFlow(gateways[s], subprocess[s_aux])
        bpmn.add_flow(flow)    
        if remove_unnecessary_gateways:
          gateways_in[subprocess[s_aux]].append(gateways[s])
          gateways_out[gateways[s]].append(subprocess[s_aux])
          flows[gateways[s], subprocess[s_aux]] = flow
      elif s!=s_aux and s in subprocess and s_aux in subprocess:
        flow = BPMN.SequenceFlow(subprocess[s], subprocess[s_aux])
        bpmn.add_flow(flow)        

  #Adds a flow from start event to gateway which represents the initial state.
  flow = BPMN.SequenceFlow(start_event, gateways[subprocessNFA.startState])
  flow.set_process(father_process)
  bpmn.add_flow(flow)

  if remove_unnecessary_gateways:
    gateways_in[subprocessNFA.startState].append(start_event)
    flows[start_event, gateways[subprocessNFA.startState]] = flow    

  #For each accepting state, adds an end event
  for s in subprocessNFA.acceptStates:
    end_events[s] = BPMN.EndEvent(name='e_'+s)
    flow = BPMN.SequenceFlow(gateways[s],end_events[s])
    bpmn.add_flow(flow)
    if remove_unnecessary_gateways:
      gateways_out[s].append(end_events[s])
      flows[gateways[s],end_events[s]] = flow    


  for s,a in subprocessNFA.transition:
    if (a!=''):
      task = BPMN.Task(name=a)
      if s in gateways:
        flow = BPMN.SequenceFlow(gateways[s], task)
        bpmn.add_flow(flow)
        if remove_unnecessary_gateways:
          gateways_out[s].append(task)
          flows[gateways[s], task] = flow    
      elif s in subprocess:
        flow = BPMN.SequenceFlow(subprocess[s], task)
        bpmn.add_flow(flow)
        if remove_unnecessary_gateways:
          gateways_out[s].append(task)
          flows[subprocess[s], task] = flow   
      for n_s in subprocessNFA.transition[s,a]:
        if n_s in gateways:
          flow = BPMN.SequenceFlow(task, gateways[n_s])
        if n_s in subprocess:
          flow = BPMN.SequenceFlow(task, subprocess[n_s])
        bpmn.add_flow(flow)
        if remove_unnecessary_gateways:
          if n_s in gateways:
            gateways_in[gateways[n_s]].append(task)
            flows[task, gateways[n_s]] = flow    
          elif n_s in subprocess:
            gateways_in[subprocess[n_s]].append(task)
            flows[task, subprocess[n_s]] = flow    

  if remove_unnecessary_gateways:
    for s in subprocessNFA.states:
      if(s in gateways and len(gateways_in[s])==1 and len(gateways_out[s])==1):
        s_in = gateways_in[s][0]
        s_out = gateways_out[s][0]
        bpmn.remove_flow(flows[s_in, gateways[s]])
        bpmn.remove_flow(flows[gateways[s], s_out])
        bpmn.add_flow(BPMN.SequenceFlow(s_in, s_out))
        bpmn.remove_node(gateways[s])

      if(s in gateways and len(gateways_in[s])==1 and len(gateways_out[s])==0):
        s_in = gateways_in[s][0]
        bpmn.remove_flow(flows[s_in, gateways[s]])
        bpmn.remove_node(gateways[s])
  
  if len(subprocess) > 0:
    for s in subprocess.keys():
      sub = subprocessNFA.NFAs.setdefault(s)
      bpmn = buildSubProcess(nfa, sub, bpmn, s, remove_unnecessary_gateways, i)
      i = i+1
  
  return bpmn


def nfaBB_to_bpmn(nfa, remove_unnecessary_gateways=True):  
  bpmn = BPMN()
  i = 1
  start_event = BPMN.StartEvent(name="i_"+str(i), isInterrupting=True)
  i = i+1
  bpmn.add_node(start_event)
  gateways = {}
  subprocess = {}
  subPro = {}
  end_events = {}
  gateways_in = {}
  gateways_out = {}
  flows = {}


  #Each state will be an exclusive gateway except those who are representing subprocesses
  for s in nfa.states:
    if s in nfa.NFAs.keys() and s not in subprocess.keys():
      subprocess[s] = BPMN.SubProcess(id=s, name=s)
      subprocess[s].set_process(nfa.label)
    elif s not in nfa.NFAs.keys():
      gateways[s] = BPMN.ExclusiveGateway(id=s, name=s)
      
    if remove_unnecessary_gateways:
      gateways_in[s] = []
      gateways_out[s] = []

  #Adds the epsilon closure flows
  for s in nfa.states:
    for s_aux in nfa.epsilon_closure[s]:
      if s!=s_aux and s in gateways and s_aux in gateways:
        flow = BPMN.SequenceFlow(gateways[s], gateways[s_aux])
        bpmn.add_flow(flow)
        if remove_unnecessary_gateways:
          gateways_in[gateways[s_aux]].append(gateways[s])
          gateways_out[gateways[s]].append(gateways[s_aux])
          flows[gateways[s], gateways[s_aux]] = flow
      elif s!=s_aux and s in subprocess and s_aux in gateways:
        flow = BPMN.SequenceFlow(subprocess[s], gateways[s_aux])
        bpmn.add_flow(flow)    
        if remove_unnecessary_gateways:
          gateways_in[gateways[s_aux]].append(subprocess[s])
          gateways_out[subprocess[s]].append(gateways[s_aux])
          flows[subprocess[s], gateways[s_aux]] = flow
      elif s!=s_aux and s in gateways and s_aux in subprocess:
        flow = BPMN.SequenceFlow(gateways[s], subprocess[s_aux])
        bpmn.add_flow(flow)    
        if remove_unnecessary_gateways:
          gateways_in[subprocess[s_aux]].append(gateways[s])
          gateways_out[gateways[s]].append(subprocess[s_aux])
          flows[gateways[s], subprocess[s_aux]] = flow
      elif s!=s_aux and s in subprocess and s_aux in subprocess:
        flow = BPMN.SequenceFlow(subprocess[s], subprocess[s_aux])
        bpmn.add_flow(flow)    

  #Creating the subprocesses inside other subprocesses
  for n in nfa.NFAs.keys():
    gatewaysSub = {}
    subprocessSub = {}
    end_eventsSub = {}
    gateways_inSub = {}
    gateways_outSub = {}
    flowsSub = {}
    sub = nfa.NFAs.setdefault(n)
    sub.set_epsilon_closure()
    start_event_sub = BPMN.StartEvent(name="i_"+str(i), isInterrupting=True)
    i = i+1
    for s in sub.states:
      if s in sub.NFAs.keys() and s not in subprocessSub.keys():
        subprocessSub[s] = BPMN.SubProcess(id=s, name=s)
        subprocessSub[s].set_process(sub.label)
      elif s not in sub.NFAs.keys():
        gatewaysSub[s] = BPMN.ExclusiveGateway(id=s+sub.label, name=s)
      if remove_unnecessary_gateways:
        gateways_inSub[s] = []
        gateways_outSub[s] = []

    #Adds the epsilon closure flows
    for s in sub.states:
      for s_aux in sub.epsilon_closure[s]:
        if s!=s_aux and s in gatewaysSub and s_aux in gatewaysSub:
          flow = BPMN.SequenceFlow(gatewaysSub[s], gatewaysSub[s_aux])
          bpmn.add_flow(flow)
          if remove_unnecessary_gateways:
            gateways_inSub[gatewaysSub[s_aux]].append(gatewaysSub[s])
            gateways_outSub[gatewaysSub[s]].append(gatewaysSub[s_aux])
            flows[gatewaysSub[s], gatewaysSub[s_aux]] = flow
        elif s!=s_aux and s in subprocess and s_aux in gatewaysSub:
          flow = BPMN.SequenceFlow(subprocessSub[s], gatewaysSub[s_aux])
          bpmn.add_flow(flow)    
          if remove_unnecessary_gateways:
            gateways_inSub[gatewaysSub[s_aux]].append(subprocessSub[s])
            gateways_outSub[subprocessSub[s]].append(gatewaysSub[s_aux])
            flows[subprocessSub[s], gatewaysSub[s_aux]] = flow
        elif s!=s_aux and s in gatewaysSub and s_aux in subprocessSub:
          flow = BPMN.SequenceFlow(gatewaysSub[s], subprocessSub[s_aux])
          bpmn.add_flow(flow)    
          if remove_unnecessary_gateways:
            gateways_inSub[subprocessSub[s_aux]].append(gatewaysSub[s])
            gateways_outSub[gatewaysSub[s]].append(subprocessSub[s_aux])
            flows[gatewaysSub[s], subprocessSub[s_aux]] = flow
        elif s!=s_aux and s in subprocessSub and s_aux in subprocessSub:
          flow = BPMN.SequenceFlow(subprocessSub[s], subprocessSub[s_aux])
          bpmn.add_flow(flow)    
        
    for s in sub.acceptStates:
      end_eventsSub[s] = BPMN.EndEvent(name='e_'+s)
      flow = BPMN.SequenceFlow(gatewaysSub[s],end_eventsSub[s])
      bpmn.add_flow(flow)
      if remove_unnecessary_gateways:
        gateways_outSub[s].append(end_eventsSub[s])
        flowsSub[gatewaysSub[s],end_eventsSub[s]] = flow    
    
    for s,a in sub.transition:
      if (a!=''):
        task = BPMN.Task(name=a)
        if s in gatewaysSub:
          flow = BPMN.SequenceFlow(gatewaysSub[s], task)
          bpmn.add_flow(flow)
          if remove_unnecessary_gateways:
            gateways_outSub[s].append(task)
            flows[gatewaysSub[s], task] = flow    
        elif s in subprocessSub:
          flow = BPMN.SequenceFlow(subprocessSub[s], task)
          bpmn.add_flow(flow)
          if remove_unnecessary_gateways:
            gateways_outSub[s].append(task)
            flows[subprocessSub[s], task] = flow
        for n_s in sub.transition[s,a]:
          if n_s in gatewaysSub:
            flow = BPMN.SequenceFlow(task, gatewaysSub[n_s])
          if n_s in subprocessSub:
            flow = BPMN.SequenceFlow(task, subprocessSub[n_s])
          bpmn.add_flow(flow)
          if remove_unnecessary_gateways:
            if n_s in gatewaysSub:
              gateways_inSub[gatewaysSub[n_s].get_name()].append(task)
              flowsSub[task, gatewaysSub[n_s]] = flow    
            elif n_s in subprocessSub:
              gateways_inSub[subprocessSub[n_s]].append(task)
              flowsSub[task, subprocessSub[n_s]] = flow
    flow = BPMN.SequenceFlow(start_event_sub, gatewaysSub[sub.startState])
    bpmn.add_flow(flow)
    



  #Adds a flow from start event to gateway which represents the initial state.
  flow = BPMN.SequenceFlow(start_event, gateways[nfa.startState])
  bpmn.add_flow(flow)

  if remove_unnecessary_gateways:
    gateways_in[nfa.startState].append(start_event)
    flows[start_event, gateways[nfa.startState]] = flow    

  #For each accepting state, adds an end event
  for s in nfa.acceptStates:
    end_events[s] = BPMN.EndEvent(name='e_'+s)
    flow = BPMN.SequenceFlow(gateways[s],end_events[s])
    bpmn.add_flow(flow)
    if remove_unnecessary_gateways:
      gateways_out[s].append(end_events[s])
      flows[gateways[s],end_events[s]] = flow    


  for s,a in nfa.transition:
    if (a!=''):
      task = BPMN.Task(name=a)
      if s in gateways:
        flow = BPMN.SequenceFlow(gateways[s], task)
        bpmn.add_flow(flow)
        if remove_unnecessary_gateways:
          gateways_out[s].append(task)
          flows[gateways[s], task] = flow    
      elif s in subprocess:
        flow = BPMN.SequenceFlow(subprocess[s], task)
        bpmn.add_flow(flow)
        if remove_unnecessary_gateways:
          gateways_out[s].append(task)
          flows[subprocess[s], task] = flow
      for n_s in nfa.transition[s,a]:
        if n_s in gateways:
          flow = BPMN.SequenceFlow(task, gateways[n_s])
        if n_s in subprocess:
          flow = BPMN.SequenceFlow(task, subprocess[n_s])
        bpmn.add_flow(flow)
        if remove_unnecessary_gateways:
          if n_s in gateways:
            gateways_in[gateways[n_s]].append(task)
            flows[task, gateways[n_s]] = flow    
          elif n_s in subprocess:
            gateways_in[subprocess[n_s]].append(task)
            flows[task, subprocess[n_s]] = flow
            

  if remove_unnecessary_gateways:
    for s in nfa.states:
      if(s in gateways and len(gateways_in[s])==1 and len(gateways_out[s])==1):
        s_in = gateways_in[s][0]
        s_out = gateways_out[s][0]
        bpmn.remove_flow(flows[s_in, gateways[s]])
        bpmn.remove_flow(flows[gateways[s], s_out])
        bpmn.add_flow(BPMN.SequenceFlow(s_in, s_out))
        bpmn.remove_node(gateways[s])

      if(s in gateways and len(gateways_in[s])==1 and len(gateways_out[s])==0):
        s_in = gateways_in[s][0]
        bpmn.remove_flow(flows[s_in, gateways[s]])
        bpmn.remove_node(gateways[s])
  

  return bpmn  
  



def fitnessAutomata(automato, df_test2, sRet=False, sRetTest=False):
  if sRetTest == False:
    
    aceita = 0
    for i in range(len(df_test2)):
      if automato.aceita(df_test2[i]):
        aceita = aceita+1

    fitness = (aceita/len(df_test2)) * 100
  
  else:
    aceita = 0
    for j in range(len(df_test2)):
      trace, trace_new_transitions = removeAllSequencesOfRepetitions(df_test2[j])
      
      if automato.aceita(trace):
        aceita = aceita+1
    fitness = (aceita/len(df_test2)) * 100

  #print("log fit:", fitness)
  return fitness



######Funções de conversão de automatos

def convertToListOfTraces(file_xes, max_traces=-1, sort=False):
      variant = xes_importer.Variants.ITERPARSE
      if(max_traces != -1):
          parameters = {variant.value.Parameters.MAX_TRACES: max_traces}
      else:
          parameters = None
      log = xes_importer.apply(file_xes, parameters)
      lLog = []
      for case_index, case in enumerate(log):
          l = []
          for event_index, event in enumerate(case):
              l.append(log[case_index][event_index]["concept:name"])
          if(lLog.__contains__(l) is False):
              lLog.append(l)
      if(sort is True):
          lLog.sort()
      return lLog


def dfaToNfa(dfa):
    states = dfa.states
    initial_states = dfa.startState
    accepting_states = dfa.acceptStates
    alphabet = dfa.alphabet
    transitions = {}
    transicoes = dfa.transition
    
    for transicao in transicoes:
      transitions.setdefault(transicao, set()).add(transicoes.setdefault(transicao))
    
    nfa = NFA_BB(states, alphabet, initial_states, transitions, accepting_states)
    return nfa


######Funções utilizadas para manipular logs



def getListOfTraces(file_csv, case_id, activity, time_timestamp, max_traces=-1):
    log_csv = pd.read_csv(file_csv, sep=',')
    log_csv = dataframe_utils.convert_timestamp_columns_in_df(log_csv)

    #Mostra as colunas do dataframe
    #print(log_csv.columns)

    #informações sobre o dataframe
    #log_csv.info()

    #print("{} Situações {}".format(len(log_csv['situacao'].unique()),log_csv['situacao'].unique()))


    log_csv = log_csv.sort_values(time_timestamp)
    log_csv.rename(columns={case_id: 'case', activity: 'concept:name',time_timestamp: 'time:timestamp'}, inplace=True)
    variant = xes_importer.Variants.ITERPARSE
    if(max_traces!=-1):
        parameters = {log_converter.Variants.TO_EVENT_LOG.value.Parameters.CASE_ID_KEY: 'case', variant.value.Parameters.MAX_TRACES: max_traces}
    else:
        parameters = {log_converter.Variants.TO_EVENT_LOG.value.Parameters.CASE_ID_KEY: 'case'}

    log = log_converter.apply(log_csv, parameters=parameters, variant=log_converter.Variants.TO_EVENT_LOG)    

    lLog  = []
    lNum = []
    for case_index, case in enumerate(log):
        l = []

        for event_index, event in enumerate(case):
            l.append(log[case_index][event_index]["concept:name"])
        b = False
        for index, lAux in enumerate(lLog):
            if(lAux.__eq__(l)):
                lNum[index] += 1
                b = True
                break
            
        if(not b):
            lLog.append(l)
            lNum.append(1)
    data = {'traces': lLog, 'number':lNum}
    df = pd.DataFrame(data)
    return df


def convertCSVToListOfTraces(file_csv, case_id, activity, time_timestamp, max_traces=-1, sort=False):
    log_csv = pd.read_csv(file_csv, sep=',')
    log_csv = dataframe_utils.convert_timestamp_columns_in_df(log_csv)
    log_csv = log_csv.sort_values(time_timestamp)
    log_csv.rename(columns={case_id: 'case', activity: 'concept:name',time_timestamp: 'time:timestamp'}, inplace=True)

    variant = xes_importer.Variants.ITERPARSE
    if(max_traces!=-1):
        parameters = {log_converter.Variants.TO_EVENT_LOG.value.Parameters.CASE_ID_KEY: 'case', variant.value.Parameters.MAX_TRACES: max_traces}
    else:
        parameters = {log_converter.Variants.TO_EVENT_LOG.value.Parameters.CASE_ID_KEY: 'case'}

    log = log_converter.apply(log_csv, parameters=parameters, variant=log_converter.Variants.TO_EVENT_LOG)    
    lLog  = []
    for case_index, case in enumerate(log):
        l = []
        for event_index, event in enumerate(case):
            l.append(log[case_index][event_index]["concept:name"])
        if(lLog.__contains__(l)==False):
            lLog.append(l)
    if(sort==True):
        lLog.sort()
    return lLog



######Funções para gerar aleatoriamente

from random import randrange
def gerar_trace(min_value, max_value, max_per_trace):
  size = randrange(1,max_per_trace)
  return [str(randrange(min_value,max_value+1)) for i in range(size)] 
def gerar_traces(min_value, max_value, max_per_trace, num_traces):
  return [gerar_trace(min_value, max_value, max_per_trace) for i in range(num_traces)]

#min_value = 1
#max_value = 9
#size = randrange(min_value,max_value+1)
#traces = 7
#tracesGerados = gerar_traces(min_value, max_value, size, traces)

#print(tracesGerados)

#nfa = toNFA(tracesGerados)

### Concatenação


def encontraSequencias(automato, umaSaida):

  cores = {}
  estados = automato.states
  finais = automato.acceptStates
  inicio = automato.startState
  saidas = automato.saidas 
  chegadas = automato.chegadas 
  destinoVarios = automato.destinoVarios
  for estado in estados:
    cores[estado] = 'b'
  aux = []
  sequencias = []
  pilha = []
  pilha.append(automato.startState)
  while len(pilha) > 0:
    estado = pilha.pop()
    cores[estado] = 'c'
    if estado in umaSaida and estado not in finais and estado != inicio:
      aux.append(estado)
      proximo = saidas.setdefault(estado)
      if len(proximo) > 0 and cores[proximo[0][1]] == 'b':
        pilha.append(proximo[0][1])
      else:
        sequencias.append(aux)
        aux = []
    else:
      proximos = saidas.setdefault(estado)
      if len(proximos) > 0:
        for prox in proximos:
          if cores[prox[1]] == 'b':
            pilha.append(prox[1])
      if len(aux) > 0:
        sequencias.append(aux)
        aux = []

  return sequencias


#Funções para transformar sequências em sub-automatos

def separaSeqBlocos(sequencias, tamanhoMaximo, tamanhoMinimo, NFAs):
  sequenciasSeparadas = []
  blocos = {}
  for sequencia in sequencias:
    if len(sequencia) > tamanhoMaximo:
      aux = []
      for estado in sequencia:
        aux.append(estado)
        if len(aux) == tamanhoMaximo:
          vdd = True
          while vdd:
            if aux[0] in NFAs.keys():
              aux.remove(aux[0])
              if len(aux) > 0 and aux[-1] in NFAs.keys():
                aux.pop()
            elif aux[0] not in NFAs.keys() and aux[-1] not in NFAs.keys():
              vdd = False
            if len(aux) == 0:
              vdd = False
          if len(aux) >= tamanhoMinimo:
            sequenciasSeparadas.append(aux)
            aux = []
      if len(aux) >= tamanhoMinimo:
        vdd = True
        while vdd:
          if aux[0] in NFAs.keys():
            aux.remove(aux[0])
            if len(aux) > 0 and aux[-1] in NFAs.keys():
              aux.pop()
          elif aux[0] not in NFAs.keys() and aux[-1] not in NFAs.keys():
            vdd = False
          if len(aux) == 0:
            vdd = False
        if len(aux) >= tamanhoMinimo:
          sequenciasSeparadas.append(aux)
          aux = []
    elif len(sequencia) >= tamanhoMinimo:
      vdd = True
      while vdd:
        if sequencia[0] in NFAs.keys():
          sequencia.remove(sequencia[0])
          if len(sequencia) > 0 and sequencia[-1] in NFAs.keys():
            sequencia.pop()
        elif sequencia[0] not in NFAs.keys() and sequencia[-1] not in NFAs.keys():
          vdd = False
        if len(sequencia) == 0:
          vdd = False
      if len(sequencia) >= tamanhoMinimo:
        sequenciasSeparadas.append(sequencia)
  
  i = len(NFAs)
  for sequencia in sequenciasSeparadas:
    blocos.setdefault('Seq' + str(i), sequencia)
    i = i + 1

  return sequenciasSeparadas, blocos


def colapsaSequencias(automato, sequencias, tamanhoMinimo=5, tamanhoMaximo=10):

  
  sequenciasSeparadas, blocos = separaSeqBlocos(sequencias, tamanhoMaximo, tamanhoMinimo, automato.NFAs)
  
  est = set()
  tra = {}
  alf = set()
  inicial = str()
  finais = set()
  nfa = {}
  saidas = {} 
  chegadas = {}


  for s in automato.states:
    est.add(s)
  for t in automato.transition.keys():
    tra.setdefault(t, automato.transition.setdefault(t))
  for n in automato.NFAs.keys():
    nfa.setdefault(n, automato.NFAs.setdefault(n))
  for a in automato.alphabet:
    alf.add(a)
  for i in automato.acceptStates:
    finais.add(i)
  

  novoAutomato = NFA_BB_Filha(est, alf, automato.startState, tra, finais, nfa)
  saidas = novoAutomato.saidas
  chegadas = novoAutomato.chegadas
  estados = novoAutomato.states
  transicoes = novoAutomato.transition
  nfas = novoAutomato.NFAs

  for bloco in blocos.keys():
    sequencia = blocos.setdefault(bloco)
    saidas[bloco] = []
    chegadas[bloco] = []
    estados.add(bloco)
    for estado in sequencia:
      estados.remove(estado)
      proximos = saidas.setdefault(estado)
      if len(proximos) > 0:
        
        for proximo in proximos:
          transicoes.pop((estado, proximo[0]))
          if proximo[1] not in sequencia:
            transicoes.setdefault((bloco, proximo[0]), set()).add(proximo[1])
            chegadas[proximo[1]].append((bloco, proximo[0]))
            chegadas[proximo[1]].remove((estado, proximo[0]))
            saidas[bloco].append(proximo)
            saidas[estado].remove(proximo)
      anteriores = chegadas.setdefault(estado)
      if len(anteriores) > 0:      
        
        for anterior in anteriores:
          if anterior in transicoes and anterior[0] not in sequencia:
            aux = transicoes.setdefault(anterior)
            estadosNRetirar = []
            for est in aux:
              if est != estado:
                estadosNRetirar.append(est)
            transicoes.pop(anterior)
            transicoes.setdefault(anterior,set()).add(bloco)
            saidas[anterior[0]].append((anterior[1], bloco))
            saidas[anterior[0]].remove((anterior[1], estado))
            chegadas[bloco].append(anterior)
            chegadas[estado].remove(anterior)
            if len(estadosNRetirar) > 0:
              for est in estadosNRetirar:
                transicoes.setdefault(anterior,set()).add(est)

  nfas2, nomeantigo = constroiSubAutomatosSeq(novoAutomato, blocos)
  nfas.update(nfas2)
  if len(nomeantigo) > 0:
    removerantigos = set()
    for s in nomeantigo.keys():
      removerantigos.add(s)
      novo = nomeantigo.setdefault(s)
      sai = saidas.setdefault(s)
      chega = chegadas.setdefault(s)
      if len(sai) > 0:
        for proximo in sai:
          if proximo[1] in nomeantigo.keys():
            transicoes.setdefault((novo, proximo[0]), set()).add(nomeantigo.setdefault(proximo[1]))
          else:
            transicoes.setdefault((novo, proximo[0]), set()).add(proximo[1])
          transicoes.pop((s, proximo[0]))
      if len(chega) > 0:
        for ant in chega:
          if ant in transicoes.keys():
            aux = transicoes.setdefault(ant)
            aux.discard(s)
            aux.add(novo)
            transicoes.update({ant:aux})
          elif ant[0] in nomeantigo.keys() and (nomeantigo.setdefault(ant[0]), ant[1]) in transicoes.keys():
            aux = transicoes.setdefault((nomeantigo.setdefault(ant[0]), ant[1]))
            aux.discard(s)
            aux.add(novo)
            transicoes.update({(nomeantigo.setdefault(ant[0]), ant[1]):aux})
    for s in removerantigos:
      estados.discard(s)
      estados.add(nomeantigo.setdefault(s))
      blocos.setdefault(nomeantigo.setdefault(s), blocos.setdefault(s))
      blocos.pop(s)
  
  
  aux = NFA_BB_Filha(estados, novoAutomato.alphabet, novoAutomato.startState, transicoes, novoAutomato.acceptStates, NFAs=nfas)
  aux.set_epsilon_closure()
  return aux

def removeElementos(lista1, lista2, minimoIgual, inicio):
  if len(lista1) < len(lista2):
    iguais = []
    for i in range(1, len(lista2)-len(lista1)):
      igual = True
      for j in range(len(lista1)):
        if lista2[i + j] != lista1[j]:
          igual = False
          break
        else:
          iguais.append(lista1[j])
          continue
      if igual and len(iguais) >= minimoIgual and i > 0 and j < len(lista2):
        return True, i, j
        
  elif len(lista1) == len(lista2):
    igual = True
    for i in range(len(lista1)):
      if lista1[i] != lista2[i]:
        igual = False
        break
    if igual:
      return True, 0, len(lista1)

  return False, None, None

def substituirRepetidos(substituir, nfas):
  dicionario = {}
  nomeantigo = {}
  for sub in substituir:
    dicionario[sub[1]] = 0
  for sub in substituir:
    k = dicionario.setdefault(sub[1])
    alvo = nfas.setdefault(sub[0])
    transicoes = []
    finais = []
    removerEstado = set()
    removerTransicao = set()
    alvo.chegadas[sub[1] + "_" + str(k)] = []
    alvo.saidas[sub[1] + "_" + str(k)] = []
    for transicao in alvo.transition.keys():
      proximos = alvo.transition.setdefault(transicao)
      if transicao[0] == alvo.startState:
        transicoes.insert(0, transicao)
      else:
        for prox in proximos:
          if prox in alvo.acceptStates:
            finais.append(transicao)
          else:
            transicoes.append(transicao)
    if sub[3] == len(alvo.transition) and sub[2] == 0:
    
      automatoContido = nfas.setdefault(sub[1])
      alvo.states = automatoContido.states
      alvo.transition = automatoContido.transition
      alvo.startState = automatoContido.startState
      alvo.acceptStates = automatoContido.acceptStates
      nomeantigo.setdefault(sub[0], sub[1] + "_" + str(k))
      alvo.label = sub[1] + "_" + str(k)
      alvo.set_epsilon_closure()
      nfas.update({sub[0]: alvo})
      nfas.setdefault(sub[1] + "_" + str(k), alvo)

    elif sub[3] < len(alvo.transition) and sub[2] > 0:
      for transicao in transicoes[sub[2]:sub[3]+sub[2]+1]:
        proximos = alvo.transition.setdefault(transicao)
        for prox in proximos:
          removerEstado.add(prox)
        removerEstado.add(transicao[0])
        removerTransicao.add(transicao)
      for i in removerTransicao:
        if i in alvo.transition:     
          alvo.transition.pop(i)
  
      for i in removerEstado:
        if i in alvo.states and alvo.saidas.setdefault(i) is not None and alvo.chegadas.setdefault(i) is not None:
          cheg = alvo.chegadas[i]
          proximos = alvo.saidas[i]
          for anterior in cheg:
            if anterior[0] not in removerEstado and anterior in alvo.transition:
              alvo.chegadas[sub[1] + "_" + str(k)].append(anterior)
              alvo.saidas[anterior[0]].append((anterior[1], sub[1] + "_" + str(k)))
              alvo.transition.pop(anterior)
              alvo.transition.setdefault(anterior,set()).add(sub[1] + "_" + str(k))
          for prox in proximos:
            if prox[1] not in removerEstado and (i, prox[0]) in alvo.transition:
              alvo.chegadas[prox[1]].append((sub[1] + "_" + str(k), prox[0]))
              alvo.saidas[sub[1] + "_" + str(k)].append(prox)
              alvo.transition.pop((i, prox[0]))
              alvo.transition.setdefault((sub[1] + "_" + str(k), prox[0]), set()).add(prox[1])
          alvo.states.discard(i)
      alvo.states.add(sub[1] + "_" + str(k))
      
      automatoContido = nfas.setdefault(sub[1])
      novosEstados = set()
      for s in automatoContido.states:
        novosEstados.add(s)
      novasTra = {}
      for t in automatoContido.transition.keys(): 
        novasTra.setdefault(t, automatoContido.transition.setdefault(t)) 
      novoAlfa = automatoContido.alphabet 
      novoIni = automatoContido.startState
      novosFins = automatoContido.acceptStates
      if len(automatoContido.NFAs) > 0:
        for n in automatoContido.NFAs.keys():
          x = automatoContido.NFAs.setdefault(n)
          
      novoAut = NFA_BB(novosEstados,novoAlfa,novoIni,novasTra,novosFins)
      alvo.states.add(sub[1] + "_" + str(k))
      alvo.NFAs.setdefault(sub[1] + "_" + str(k), novoAut)
      
      novoAut.nfa_parent = alvo
      novoAut.label = sub[1] + "_" + str(k)
      novoAut.set_epsilon_closure()
      nfas.update({sub[0]: alvo})
      alvo.set_epsilon_closure()
    dicionario.update({sub[1]: k+1})
  return nfas, nomeantigo


    

def subRepetidos(nfas, minimoIgual = 4):
  substituir = []
  guardados = []
  nomeantigo = {}
  fimSubSeq = {}
  aux = {}
  for i in nfas.keys():
    fimSubSeq[i] = []
  for i in nfas.keys():
    teste1 = nfas.setdefault(i)
    sequenciaAcoes1 = []
    for transicao in teste1.transition.keys():
      sequenciaAcoes1.append(transicao[1])
    for j in nfas.keys():
      if i != j:
        teste2 = nfas.setdefault(j)  
        sequenciaAcoes2 = []
        for transicao in teste2.transition.keys():
          sequenciaAcoes2.append(transicao[1])
        sublista, inicio, fim = removeElementos(sequenciaAcoes1, sequenciaAcoes2, minimoIgual, nfas[j].startState)
        if sublista == True and (j,i) not in guardados and (i,j) not in guardados:
          if len(fimSubSeq[j]) > 0:
            limite = True
            retirar = []
            for limites in fimSubSeq[j]:
              if fim-inicio < limites[1]-limites[0]:
                if inicio > limites[0] and fim < limites[1]:
                  limite=False
                elif inicio < limites[0] and fim <= limites[1] and fim >= limites[0]:
                  limite=False
                elif inicio >= limites[0] and inicio <= limites[1] and fim > limites[1]:
                  limite=False
              else:
                if inicio < limites[0] and fim > limites[1]:
                  quadrupla = aux.setdefault((j, limites[0], limites[1]))
                  if quadrupla in substituir:
                    substituir.remove(quadrupla)
                  retirar.append(limites)
                elif inicio < limites[0] and fim < limites[1] and fim >= limites[0]:
                  quadrupla = aux.setdefault((j, limites[0], limites[1]))
                  if quadrupla in substituir:
                    substituir.remove(quadrupla)
                  retirar.append(limites)
                elif inicio >= limites[0] and inicio <= limites[1] and fim > limites[1]:
                  quadrupla = aux.setdefault((j, limites[0], limites[1]))
                  if quadrupla in substituir:
                    substituir.remove(quadrupla)
                  retirar.append(limites)
            if limite:
              if len(retirar) > 0:
                for limites in retirar:
                  fimSubSeq.setdefault(j, []).remove(limites)
              substituir.append((j, i, inicio, fim))
              fimSubSeq.setdefault(j, []).append((inicio, fim))
              aux.setdefault((j, inicio, fim), (j,i,inicio,fim))
              guardados.append((j, i))
          else:
            substituir.append((j, i, inicio, fim))
            fimSubSeq.setdefault(j, []).append((inicio, fim))
            aux.setdefault((j, inicio, fim), (j,i,inicio,fim))
            guardados.append((j, i))
  if len(substituir) > 0:
    nfas, nomeantigo = substituirRepetidos(substituir, nfas)
  return nfas, nomeantigo
      

def constroiSubAutomatosSeq(automato, blocos):
  NFAs = {}
  saidas = automato.saidas
  for bloco in blocos.keys():
    sequencia = blocos.setdefault(bloco)
    states = set()
    alphabet = set()#automato.alphabet
    initial_state = sequencia[0]
    transitions = {}
    accepting_states = set()
    for estado in sequencia:
      states.add(estado)
      proximo = saidas.setdefault(estado)
      if len(proximo) > 0:
        for prox in proximo:
          if prox[1] in sequencia:
            transitions.setdefault((estado, prox[0]), set()).add(prox[1])
            alphabet.add(prox[0])
          else:
            accepting_states.add(estado)
      else:
        accepting_states.add(estado)
    Np = NFA_BB_Filha(states,alphabet,initial_state,transitions,accepting_states)
    Np.nfa_parent = automato
    Np.label = bloco
    NFAs.setdefault(bloco, Np)

  NFAs, nomeantigo = subRepetidos(NFAs)
  return NFAs, nomeantigo

def verificaSequencias(automato, tamanhoMinimo):
  saidas = automato.saidas
  chegadas = automato.chegadas 
  umaSaida = automato.umaSaida
  destinoVarios = automato.destinoVarios
  estadosCandidatosAux = set(umaSaida).difference(set(destinoVarios))
  estadosCandidatos = estadosCandidatosAux.difference(automato.acceptStates)
  nfas = automato.NFAs
  if automato.startState in estadosCandidatos:
    estadosCandidatos.discard(automato.startState)
  erros = []
  errado = False
  if len(estadosCandidatos) > 0:
    cores = {}
    for s in automato.states:
      cores.setdefault(s, 'b')

    pilha = []
    aux= []
    pilha.append(automato.startState)
    while len(pilha) > 0:
      estado = pilha.pop()
      cores[estado] = 'c'
      if estado in estadosCandidatos:
        aux.append(estado)
      elif len(aux) >= tamanhoMinimo:
        if len(nfas) > 0:
          vdd = True
          while vdd:
            if len(aux) > 0 and aux[0] in nfas.keys():
              aux.remove(aux[0])
            if len(aux) > 0 and aux[-1] in nfas.keys():
              aux.pop()
            if len(aux) > 0 and aux[0] not in nfas.keys() and aux[-1] not in nfas.keys():
              vdd = False
            if len(aux) == 0:
              vdd = False
          if len(aux) >= tamanhoMinimo:
            erros.append(aux)
          aux = []
        else:
          erros.append(aux)
          aux = []
      elif len(aux) < tamanhoMinimo:
        aux = []
      proximos = saidas.setdefault(estado)
      for proximo in proximos:
        if proximo[1] in automato.states:
          if cores[proximo[1]] == 'b':
            pilha.append(proximo[1])
          elif len(aux) >= tamanhoMinimo:
            if len(nfas) > 0:
              vdd = True
              while vdd:
                if len(aux) > 0 and aux[0] in nfas.keys():
                  aux.remove(aux[0])
                if len(aux) > 0 and aux[-1] in nfas.keys():
                  aux.pop()
                if len(aux) > 0 and aux[0] not in nfas.keys() and aux[-1] not in nfas.keys():
                  vdd = False
                if len(aux) == 0:
                  vdd = False
              if len(aux) >= tamanhoMinimo:
                erros.append(aux)
              aux = []
            else:
              erros.append(aux)
              aux = []
          elif len(aux) < tamanhoMinimo:
            aux = []

    if len(erros) > 0:
      errado = True
  return errado, erros
  

def operacaoSequencias(automato_e, tamanhoMinimo, tamanhoMaximo):
  if tamanhoMaximo >= tamanhoMinimo:
    automato = NFA_BB_Filha(automato_e.states, automato_e.alphabet, automato_e.startState, automato_e.transition, automato_e.acceptStates)
    umaSaida = automato.umaSaida
    umaSaida = set(umaSaida).difference(set(automato.NFAs.keys()))
    sequencias = encontraSequencias(automato, umaSaida)
    if len(sequencias) > 0:
      finais = automato.acceptStates
      for sequencia in sequencias:
        if automato.startState in sequencia:
          return automato
        if len(finais & set(sequencia)) > 0:
          return automato
      novoAutomato = colapsaSequencias(automato, sequencias, tamanhoMinimo, tamanhoMaximo)


      novoAutomato.set_epsilon_closure()      

      errado, erros = verificaSequencias(novoAutomato, tamanhoMinimo)
      print("TÁ ERRADO?", errado, erros)


      return novoAutomato
    else:
      return automato
  else:
    return automato

def countBPMN(bpmn):
  gateways = []
  tasks = []
  for n in bpmn.get_nodes():
    if type(n) == pm4py.objects.bpmn.obj.BPMN.Task:
      tasks.append(n)
    elif type(n) == pm4py.objects.bpmn.obj.BPMN.ExclusiveGateway:
      gateways.append(n)
    elif type(n) == pm4py.objects.bpmn.obj.BPMN.ParallelGateway:
      gateways.append(n)
  return len(gateways), len(tasks), len(bpmn.get_flows())


def tabelamentoBPMN(bpmn):
  resultadosBPMN = []
  gateways, tasks, flows = countBPMN(bpmn)
  resultadosBPMN.append(["BPMN algoritmo", gateways, tasks, flows, gateways+tasks])
  
  outBPMN = widgets.Output()

  
  tabsBPMN = widgets.Tab(children=[outBPMN])
  tabsBPMN.set_title(0, 'BPMN')
  display(tabsBPMN)
  with outBPMN:

    display(pd.DataFrame(resultadosBPMN,columns=[" ", "Gateways","Tasks","Transições", "Componentes"]))





def tabelamento(event_log, df_test, sRetTest = True, camMin=True, sRet=True, join=True, mFreq=False, p=1, remGat = True):


  #Caminhos mais frequêntes
  if mFreq:
    l_mf_traces, acuracia = get_most_frequent_traces(event_log,percentage=p)
    print(f"Frequencia por trace dos {p*100}% mais frequentes:\n",l_mf_traces)
    #print(f"{p*100}% dos traces mais frequentes:\n",[x[0] for x in l_mf_traces])
    event_logFreq = [x[0] for x in l_mf_traces]

    resultados = []
    resultadosBPMN = []
    nfa = to_nfa(event_logFreq)
    fit = fitnessAutomata(nfa, df_test, sRet, sRetTest)
    resultados.append([f"Não-Determinística",len(nfa.alphabet),len(nfa.states),nfa.len_transition(),len(nfa.acceptStates), 0, nfa.len_states(), fit])
    bpmn = nfa_to_bpmn(nfa, remGat)
    gateways, tasks, flows = countBPMN(bpmn)
    resultadosBPMN.append([f"Não-Determinística", gateways, tasks, flows, gateways+tasks])
    dfa = nfa.determinization()
    dfa.rename()
    fit = fitnessAutomata(dfa, df_test, sRet, sRetTest)
    resultados.append([f"Determinística",len(dfa.alphabet),len(dfa.states),len(dfa.transition),len(dfa.acceptStates), "-", "-", fit])
    bpmn = dfa_to_bpmn(dfa, remGat)
    gateways, tasks, flows = countBPMN(bpmn)
    resultadosBPMN.append([f"Determinística", gateways, tasks, flows, gateways+tasks])
    

    min= dfa.minimization()
    min.rename()
    fit = fitnessAutomata(min, df_test, sRet, sRetTest)
    resultados.append([f"Determinística min",len(min.alphabet),len(min.states),len(min.transition),len(min.acceptStates), "-", "-", fit])
    bpmn = dfa_to_bpmn(min, remGat)
    gateways, tasks, flows = countBPMN(bpmn)
    resultadosBPMN.append([f"Determinística min", gateways, tasks, flows, gateways+tasks])
    


    min = dfaToNfa(min)
    nfaResultado = operacaoSequencias(min, 3, 25)
    fit = fitnessAutomata(nfaResultado, df_test, sRet, sRetTest)
    resultados.append([f"Operação Sequencias min/max:3-25 estados DFA min",len(nfaResultado.alphabet),len(nfaResultado.states),len(nfaResultado.transition),len(nfaResultado.acceptStates), len(nfaResultado.NFAs), nfaResultado.len_states(), fit])
    bpmn = nfaBB_to_bpmn(nfaResultado, remGat)
    gateways, tasks, flows = countBPMN(bpmn)
    resultadosBPMN.append([f"Operação Sequencias min/max:3-25 estados DFA min", gateways, tasks, flows, gateways+tasks])
    
    
    #Caminho Mínimo
    if camMin:
      nfaCamMin = to_nfa_minimum_path(event_logFreq, nfa_bb=False)
      fit = fitnessAutomata(nfaCamMin, df_test, sRet, sRetTest)
      resultados.append([f"Não-Determinística caminho mínimo",len(nfaCamMin.alphabet),len(nfaCamMin.states),nfaCamMin.len_transition(),len(nfaCamMin.acceptStates), 0, "-", fit])
      bpmn = nfa_to_bpmn(nfaCamMin, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Não-Determinística caminho mínimo", gateways, tasks, flows, gateways+tasks])
      
      
      dfa = nfaCamMin.determinization()
      #print(dfa.alphabet)
      dfa.rename()
      fit = fitnessAutomata(dfa, df_test, sRet, sRetTest)
      resultados.append([f"Determinística",len(dfa.alphabet),len(dfa.states),len(dfa.transition),len(dfa.acceptStates), "-", "-", fit])
      bpmn = dfa_to_bpmn(dfa, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Determinística", gateways, tasks, flows, gateways+tasks])
      


      min = dfa.minimization()
      fit = fitnessAutomata(min, df_test, sRet, sRetTest)
      resultados.append([f"Determinística min",len(min.alphabet),len(min.states),len(min.transition),len(min.acceptStates), "-", "-", fit])
      bpmn = dfa_to_bpmn(min, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Determinística min", gateways, tasks, flows, gateways+tasks])
      


      min = dfaToNfa(min)
      nfaResultado = operacaoSequencias(min, 3, 25)
      fit = fitnessAutomata(nfaResultado, df_test, sRet, sRetTest)
      resultados.append([f"Operação Sequencias min/max:3-25 estados DFA min caminhos mínimos",len(nfaResultado.alphabet),len(nfaResultado.states),len(nfaResultado.transition),len(nfaResultado.acceptStates), len(nfaResultado.NFAs), nfaResultado.len_states(), fit])
      bpmn = nfaBB_to_bpmn(nfaResultado, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Operação Sequencias min/max:3-25 estados DFA min caminhos mínimos", gateways, tasks, flows, gateways+tasks])
      


    #Sem retrabalho
    if sRet:
      nfaReworkFalse = to_nfa_minimum_path(event_logFreq, rework=False, nfa_bb=False)
      fit = fitnessAutomata(nfaReworkFalse, df_test, sRet, sRetTest)
      resultados.append([f"Não-Determinística sem retrabalho",len(nfaReworkFalse.alphabet),len(nfaReworkFalse.states),nfaReworkFalse.len_transition(),len(nfaReworkFalse.acceptStates), 0, nfaReworkFalse.len_states(), fit])
      bpmn = nfa_to_bpmn(nfaReworkFalse, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Não-Determinística sem retrabalho", gateways, tasks, flows, gateways+tasks])
      


      dfaFalse = nfaReworkFalse.determinization()
      #print(dfa.alphabet)
      dfaFalse.rename()
      fit = fitnessAutomata(dfaFalse, df_test, sRet, sRetTest)
      resultados.append([f"Determinística s retrabalho",len(dfaFalse.alphabet),len(dfaFalse.states),len(dfaFalse.transition),len(dfaFalse.acceptStates), "-", "-", fit])
      bpmn = dfa_to_bpmn(dfaFalse, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Determinística s retrabalho", gateways, tasks, flows, gateways+tasks])
      


      minFalse= dfaFalse.minimization()
      minFalse.rename()
      fit = fitnessAutomata(minFalse, df_test, sRet, sRetTest)
      resultados.append([f"Determinística min s retrabalho",len(minFalse.alphabet),len(minFalse.states),len(minFalse.transition),len(minFalse.acceptStates), "-", "-", fit])
      bpmn = dfa_to_bpmn(minFalse, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Determinística min s retrabalho", gateways, tasks, flows, gateways+tasks])
      


      min = dfaToNfa(minFalse)
      nfaResultado = operacaoSequencias(min, 3, 25)
      fit = fitnessAutomata(nfaResultado, df_test, sRet, sRetTest)
      resultados.append([f"Operação Sequencias min/max:3-25 estados DFA min sem retrabalho",len(nfaResultado.alphabet),len(nfaResultado.states),len(nfaResultado.transition),len(nfaResultado.acceptStates), len(nfaResultado.NFAs), nfaResultado.len_states(), fit])
      bpmn = nfaBB_to_bpmn(nfaResultado, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Operação Sequencias min/max:3-25 estados DFA min sem retrabalho", gateways, tasks, flows, gateways+tasks])
      

    #Sem caminhos repetidos
    if join:
      nfaJoin = to_nfa_minimum_path_join_traces(event_logFreq)
      fit = fitnessAutomata(nfaJoin, df_test, sRet, sRetTest)
      resultados.append([f"Não-Determinística join",len(nfaJoin.alphabet),len(nfaJoin.states),nfaJoin.len_transition(),len(nfaJoin.acceptStates), 0, "-", fit])
      bpmn = nfa_to_bpmn(nfaJoin, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Não-Determinística join", gateways, tasks, flows, gateways+tasks])
      


      dfaJoin = nfaJoin.determinization()
      dfaJoin.rename()
      fit = fitnessAutomata(dfaJoin, df_test, sRet, sRetTest)
      resultados.append([f"Determinística join",len(nfaJoin.alphabet),len(nfaJoin.states),len(nfaJoin.transition),len(nfaJoin.acceptStates), "-" , "-", fit])
      bpmn = dfa_to_bpmn(dfaJoin, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Determinística join", gateways, tasks, flows, gateways+tasks])
      


      minJoin= dfaJoin.minimization()
      minJoin.rename()
      fit = fitnessAutomata(minJoin, df_test, sRet, sRetTest)
      resultados.append([f"Determinística min join",len(minJoin.alphabet),len(minJoin.states),len(minJoin.transition),len(minJoin.acceptStates), "-", "-", fit])
      bpmn = dfa_to_bpmn(minJoin, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Determinística min join", gateways, tasks, flows, gateways+tasks])
      


      min = dfaToNfa(minJoin)
      nfaResultado = operacaoSequencias(min, 3, 25)
      fit = fitnessAutomata(nfaResultado, df_test, sRet, sRetTest)
      resultados.append([f"Operação Sequencias min/max:3-25 estados DFA min join",len(nfaResultado.alphabet),len(nfaResultado.states),len(nfaResultado.transition),len(nfaResultado.acceptStates), len(nfaResultado.NFAs), nfaResultado.len_states(), fit])
      bpmn = nfaBB_to_bpmn(min, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append([f"Operação Sequencias min/max:3-25 estados DFA min join", gateways, tasks, flows, gateways+tasks])
      

      if sRet:
        nfaJoinFalse = to_nfa_minimum_path_join_traces(event_logFreq, rework=False)
        fit = fitnessAutomata(nfaJoinFalse, df_test, sRet, sRetTest)
        resultados.append([f"Não-Determinística sem retrabalho join",len(nfaJoinFalse.alphabet),len(nfaJoinFalse.states),nfaJoinFalse.len_transition(),len(nfaJoinFalse.acceptStates), 0,"-", fit])
        bpmn = nfa_to_bpmn(nfaJoinFalse, remGat)
        gateways, tasks, flows = countBPMN(bpmn)
        resultadosBPMN.append([f"Não-Determinística sem retrabalho join", gateways, tasks, flows, gateways+tasks])
        
        
        dfaJoinFalse = nfaJoinFalse.determinization()
        dfaJoinFalse.rename()
        fit = fitnessAutomata(dfaJoinFalse, df_test, sRet, sRetTest)
        resultados.append([f"Determinística sem retrabalho join",len(dfaJoinFalse.alphabet),len(dfaJoinFalse.states),len(dfaJoinFalse.transition),len(dfaJoinFalse.acceptStates), "-", "-", fit])
        bpmn = dfa_to_bpmn(dfaJoinFalse, remGat)
        gateways, tasks, flows = countBPMN(bpmn)
        resultadosBPMN.append([f"Determinística sem retrabalho join", gateways, tasks, flows, gateways+tasks])
        


        minJoinFalse= dfaJoinFalse.minimization()
        minJoinFalse.rename()
        fit = fitnessAutomata(minJoinFalse, df_test, sRet, sRetTest)
        resultados.append([f"Determinística min sem retrabalho join",len(minJoinFalse.alphabet),len(minJoinFalse.states),len(minJoinFalse.transition),len(minJoinFalse.acceptStates), "-", "-", fit])
        bpmn = dfa_to_bpmn(minJoinFalse, remGat)
        gateways, tasks, flows = countBPMN(bpmn)
        resultadosBPMN.append([f"Determinística min sem retrabalho join", gateways, tasks, flows, gateways+tasks])
        


        min = dfaToNfa(minJoinFalse)
        nfaResultado = operacaoSequencias(min, 3, 25)
        fit = fitnessAutomata(nfaResultado, df_test, sRet, sRetTest)
        resultados.append([f"Operação Sequencias min/max:3-25 estados DFA min sem retrabalho join",len(nfaResultado.alphabet),len(nfaResultado.states),len(nfaResultado.transition),len(nfaResultado.acceptStates), len(nfaResultado.NFAs), nfaResultado.len_states(), fit])
        bpmn = nfaBB_to_bpmn(min, remGat)
        gateways, tasks, flows = countBPMN(bpmn)
        resultadosBPMN.append([f"Operação Sequencias min/max:3-25 estados DFA min sem retrabalho join", gateways, tasks, flows, gateways+tasks])
        
  
  else:
    resultados = []
    resultadosBPMN = []
    nfa = to_nfa(event_log)

    fit = fitnessAutomata(nfa, df_test, sRet, sRetTest)
    resultados.append(["Não-Determinística",len(nfa.alphabet),len(nfa.states),nfa.len_transition(),len(nfa.acceptStates), 0, nfa.len_states(), fit])
    
    
    bpmn = nfa_to_bpmn(nfa, remGat)
    gateways, tasks, flows = countBPMN(bpmn)
    resultadosBPMN.append(["Não-Determinística", gateways, tasks, flows, gateways+tasks])
    
    dfa = nfa.determinization()
    dfa.rename()
    fit = fitnessAutomata(dfa, df_test, sRet, sRetTest)
    resultados.append(["Determinística",len(dfa.alphabet),len(dfa.states),len(dfa.transition),len(dfa.acceptStates), "-", "-", fit])
    bpmn = dfa_to_bpmn(dfa, remGat)
    gateways, tasks, flows = countBPMN(bpmn)
    resultadosBPMN.append(["Determinística", gateways, tasks, flows, gateways+tasks])
    


    min= dfa.minimization()
    min.rename()
    fit = fitnessAutomata(min, df_test, sRet, sRetTest)
    resultados.append(["Determinística min",len(min.alphabet),len(min.states),len(min.transition),len(min.acceptStates), "-", "-", fit])
    bpmn = dfa_to_bpmn(min, remGat)
    gateways, tasks, flows = countBPMN(bpmn)
    resultadosBPMN.append(["Determinística min", gateways, tasks, flows, gateways+tasks])
    


    min = dfaToNfa(min)
    nfaResultado = operacaoSequencias(min, 3, 25)
    fit = fitnessAutomata(nfaResultado, df_test, sRet, sRetTest)
    resultados.append(["Operação Sequencias min/max:3-25 estados DFA min",len(nfaResultado.alphabet),len(nfaResultado.states),len(nfaResultado.transition),len(nfaResultado.acceptStates), len(nfaResultado.NFAs), nfaResultado.len_states(), fit])
    bpmn = nfaBB_to_bpmn(nfaResultado, remGat)
    gateways, tasks, flows = countBPMN(bpmn)
    resultadosBPMN.append(["Operação Sequencias min/max:3-25 estados DFA min", gateways, tasks, flows, gateways+tasks])
    


    #Caminho Mínimo
    if camMin:
      nfaCamMin = to_nfa_minimum_path(event_log, nfa_bb=False)
      fit = fitnessAutomata(nfaCamMin, df_test, sRet, sRetTest)
      resultados.append(["Não-Determinística caminho mínimo",len(nfaCamMin.alphabet),len(nfaCamMin.states),nfaCamMin.len_transition(),len(nfaCamMin.acceptStates), 0, "-", fit])
      bpmn = nfa_to_bpmn(nfaCamMin, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Não-Determinística caminho mínimo", gateways, tasks, flows, gateways+tasks])
      

      dfa = nfaCamMin.determinization()
      dfa.rename()
      fit = fitnessAutomata(dfa, df_test, sRet, sRetTest)
      resultados.append(["Determinística",len(dfa.alphabet),len(dfa.states),len(dfa.transition),len(dfa.acceptStates), "-", "-", fit])
      bpmn = dfa_to_bpmn(dfa, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Determinística", gateways, tasks, flows, gateways+tasks])
      


      min = dfa.minimization()
      fit = fitnessAutomata(min, df_test, sRet, sRetTest)
      resultados.append(["Determinística min",len(min.alphabet),len(min.states),len(min.transition),len(min.acceptStates), "-", "-", fit])
      bpmn = dfa_to_bpmn(min, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Determinística min", gateways, tasks, flows, gateways+tasks])
      


      min = dfaToNfa(min)
      nfaResultado = operacaoSequencias(min, 3, 25)
      fit = fitnessAutomata(nfaResultado, df_test, sRet, sRetTest)
      resultados.append(["Operação Sequencias min/max:3-25 estados DFA min caminhos mínimos",len(nfaResultado.alphabet),len(nfaResultado.states),len(nfaResultado.transition),len(nfaResultado.acceptStates), len(nfaResultado.NFAs), nfaResultado.len_states(), fit])
      bpmn = nfaBB_to_bpmn(nfaResultado, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Operação Sequencias min/max:3-25 estados DFA min caminhos mínimos", gateways, tasks, flows, gateways+tasks])
      


    #Sem retrabalho
    if sRet:
      nfaReworkFalse = to_nfa_minimum_path(event_log, rework=False, nfa_bb=False)
      fit = fitnessAutomata(nfaReworkFalse, df_test, sRet, sRetTest)
      resultados.append(["Não-Determinística sem retrabalho",len(nfaReworkFalse.alphabet),len(nfaReworkFalse.states),nfaReworkFalse.len_transition(),len(nfaReworkFalse.acceptStates), 0, nfaReworkFalse.len_states(), fit])
      bpmn = nfa_to_bpmn(nfaReworkFalse, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Não-Determinística sem retrabalho", gateways, tasks, flows, gateways+tasks])
      


      dfaFalse = nfaReworkFalse.determinization()
      #print(dfa.alphabet)
      dfaFalse.rename()
      fit = fitnessAutomata(dfaFalse, df_test, sRet, sRetTest)
      resultados.append(["Determinística s retrabalho",len(dfaFalse.alphabet),len(dfaFalse.states),len(dfaFalse.transition),len(dfaFalse.acceptStates), "-", "-", fit])
      bpmn = dfa_to_bpmn(dfaFalse, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Determinística s retrabalho", gateways, tasks, flows, gateways+tasks])
      


      minFalse= dfaFalse.minimization()
      minFalse.rename()
      fit = fitnessAutomata(minFalse, df_test, sRet, sRetTest)
      resultados.append(["Determinística min s retrabalho",len(minFalse.alphabet),len(minFalse.states),len(minFalse.transition),len(minFalse.acceptStates), "-", "-", fit])
      bpmn = dfa_to_bpmn(minFalse, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Determinística min s retrabalho", gateways, tasks, flows, gateways+tasks])
      


      min = dfaToNfa(minFalse)
      nfaResultado = operacaoSequencias(min, 3, 25)
      fit = fitnessAutomata(nfaResultado, df_test, sRet, sRetTest)
      resultados.append(["Operação Sequencias min/max:3-25 estados DFA min sem retrabalho",len(nfaResultado.alphabet),len(nfaResultado.states),len(nfaResultado.transition),len(nfaResultado.acceptStates), len(nfaResultado.NFAs), nfaResultado.len_states(), fit])
      bpmn = nfaBB_to_bpmn(nfaResultado, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Operação Sequencias min/max:3-25 estados DFA min sem retrabalho", gateways, tasks, flows, gateways+tasks])
      


    #Sem caminhos repetidos
    if join:
      nfaJoin = to_nfa_minimum_path_join_traces(event_log)
      fit = fitnessAutomata(nfaJoin, df_test, sRet, sRetTest)
      resultados.append(["Não-Determinística join",len(nfaJoin.alphabet),len(nfaJoin.states),nfaJoin.len_transition(),len(nfaJoin.acceptStates), 0, "-", fit])
      bpmn = nfa_to_bpmn(nfaJoin, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Não-Determinística join", gateways, tasks, flows, gateways+tasks])
      


      dfaJoin = nfaJoin.determinization()
      dfaJoin.rename()
      fit = fitnessAutomata(dfaJoin, df_test, sRet, sRetTest)
      resultados.append(["Determinística join",len(nfaJoin.alphabet),len(nfaJoin.states),len(nfaJoin.transition),len(nfaJoin.acceptStates), "-" , "-", fit])
      bpmn = dfa_to_bpmn(dfaJoin, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Determinística join", gateways, tasks, flows, gateways+tasks])
      


      minJoin= dfaJoin.minimization()
      minJoin.rename()
      fit = fitnessAutomata(minJoin, df_test, sRet, sRetTest)
      resultados.append(["Determinística min join",len(minJoin.alphabet),len(minJoin.states),len(minJoin.transition),len(minJoin.acceptStates), "-", "-", fit])
      bpmn = dfa_to_bpmn(minJoin, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Determinística min join", gateways, tasks, flows, gateways+tasks])
      


      min = dfaToNfa(minJoin)
      nfaResultado = operacaoSequencias(min, 3, 25)
      fit = fitnessAutomata(nfaResultado, df_test, sRet, sRetTest)
      resultados.append(["Operação Sequencias min/max:3-25 estados DFA min join",len(nfaResultado.alphabet),len(nfaResultado.states),len(nfaResultado.transition),len(nfaResultado.acceptStates), len(nfaResultado.NFAs), nfaResultado.len_states(), fit])
      bpmn = nfaBB_to_bpmn(nfaResultado, remGat)
      gateways, tasks, flows = countBPMN(bpmn)
      resultadosBPMN.append(["Operação Sequencias min/max:3-25 estados DFA min join", gateways, tasks, flows, gateways+tasks])
      


      if sRet:
        nfaJoinFalse = to_nfa_minimum_path_join_traces(event_log, rework=False)
        fit = fitnessAutomata(nfaJoinFalse, df_test, sRet, sRetTest)
        resultados.append(["Não-Determinística sem retrabalho join",len(nfaJoinFalse.alphabet),len(nfaJoinFalse.states),nfaJoinFalse.len_transition(),len(nfaJoinFalse.acceptStates), 0,"-"])
        bpmn = nfa_to_bpmn(nfaJoinFalse, remGat)
        gateways, tasks, flows = countBPMN(bpmn)
        resultadosBPMN.append(["Não-Determinística sem retrabalho join", gateways, tasks, flows, gateways+tasks])
        
        
        dfaJoinFalse = nfaJoinFalse.determinization()
        #print(dfa.alphabet)
        dfaJoinFalse.rename()
        fit = fitnessAutomata(dfaJoinFalse, df_test, sRet, sRetTest)
        resultados.append(["Determinística sem retrabalho join",len(dfaJoinFalse.alphabet),len(dfaJoinFalse.states),len(dfaJoinFalse.transition),len(dfaJoinFalse.acceptStates), "-", "-", fit])
        bpmn = dfa_to_bpmn(dfaJoinFalse, remGat)
        gateways, tasks, flows = countBPMN(bpmn)
        resultadosBPMN.append(["Determinística sem retrabalho join", gateways, tasks, flows, gateways+tasks])
      


        minJoinFalse= dfaJoinFalse.minimization()
        minJoinFalse.rename()
        fit = fitnessAutomata(minJoinFalse, df_test, sRet, sRetTest)
        resultados.append(["Determinística min sem retrabalho join",len(minJoinFalse.alphabet),len(minJoinFalse.states),len(minJoinFalse.transition),len(minJoinFalse.acceptStates), "-", "-", fit])
        bpmn = dfa_to_bpmn(minJoinFalse, remGat)
        gateways, tasks, flows = countBPMN(bpmn)
        resultadosBPMN.append(["Determinística min sem retrabalho join", gateways, tasks, flows, gateways+tasks])
        


        min = dfaToNfa(minJoinFalse)
        nfaResultado= operacaoSequencias(min, 3, 25)
        fit = fitnessAutomata(nfaResultado, df_test, sRet, sRetTest)
        resultados.append(["Operação Sequencias min/max:3-25 estados DFA min sem retrabalho join",len(nfaResultado.alphabet),len(nfaResultado.states),len(nfaResultado.transition),len(nfaResultado.acceptStates), len(nfaResultado.NFAs), nfaResultado.len_states(), fit])
        bpmn = nfaBB_to_bpmn(nfaResultado, remGat)
        gateways, tasks, flows = countBPMN(bpmn)
        resultadosBPMN.append(["Operação Sequencias min/max:3-25 estados DFA min sem retrabalho join", gateways, tasks, flows, gateways+tasks])
    

  outMaquinaEstado = widgets.Output()

  
  tabs = widgets.Tab(children=[outMaquinaEstado])
  tabs.set_title(0, 'Máquina de Estados')
  display(tabs)
  with outMaquinaEstado:
    text = "Tam log: " + str(len(event_log))
    if mFreq:
      textfreq = "Frequência: "+ str(get_most_frequent_traces(event_log, percentage=p)[1])
    sum = 0
    for x in event_log:
      sum+=len(x)
    textSum = "N° eventos: " + str(sum)
    


    display(text)
    if mFreq:
      display(textfreq)

    display(textSum)
    display(pd.DataFrame(resultados,columns=["Máquina de Estados","Atividades","Estados","Transições","Estados de Aceitação", "Sub-Automatos", "Estados + Estados sub", "Acurácia"]))

  outBPMN = widgets.Output()

  
  tabsBPMN = widgets.Tab(children=[outBPMN])
  tabsBPMN.set_title(0, 'BPMN')
  display(tabsBPMN)
  with outBPMN:
    text = "Tam log: " + str(len(event_log))
    if mFreq:
      textfreq = "Frequência: " + str(get_most_frequent_traces(event_log, percentage=p)[1])
    sum = 0
    for x in event_log:
      sum+=len(x)
    textSum = "N° eventos: " + str(sum)


    display(text)


    if mFreq:
      display(textfreq)

    display(textSum)

    display(pd.DataFrame(resultadosBPMN,columns=["Referente à:", "Gateways","Tasks","Transições","Componentes"]))


def comparacao(bpmnAlpha, bpmnHeu, bpmnInd, fitAlpha, fitHeu, fitInd, train_csv, test_csv, camMin=True, sRet=True, join=True):
  comparacaoBPMN = []
  gateways, tasks, flows = countBPMN(bpmnAlpha)
  comparacaoBPMN.append([f"Alpha miner BPMN", gateways, tasks, flows, gateways+tasks, fitAlpha])

  gateways, tasks, flows = countBPMN(bpmnHeu)
  comparacaoBPMN.append([f"Heuristic miner BPMN", gateways, tasks, flows, gateways+tasks, fitHeu])

  gateways, tasks, flows = countBPMN(bpmnInd)
  comparacaoBPMN.append([f"Inductive miner BPMN", gateways, tasks, flows, gateways+tasks, fitInd])

  if join:
    if sRet:
      nfaJoinFalse = to_nfa_minimum_path_join_traces(train_csv, rework=False)
      
      
      dfaJoinFalse = nfaJoinFalse.determinization()
      


      minJoinFalse= dfaJoinFalse.minimization()
      minJoinFalse.rename()
      


      min = dfaToNfa(minJoinFalse)
      nfaResultado= operacaoSequencias(min, 3, 25)
      fit = fitnessAutomata(nfaResultado, test_csv, sRet, sRetTest=False)
      bpmn = nfaBB_to_bpmn(nfaResultado)
      gateways, tasks, flows = countBPMN(bpmn)
      comparacaoBPMN.append(["Operação Sequencias min/max:3-25 estados DFA min sem retrabalho join", gateways, tasks, flows, gateways+tasks, fit])
    else:
      nfaJoin = to_nfa_minimum_path_join_traces(train_csv, rework=True)
      
      
      dfaJoin = nfaJoin.determinization()
      


      minJoin= dfaJoin.minimization()
      minJoin.rename()
      


      min = dfaToNfa(minJoin)
      nfaResultado= operacaoSequencias(min, 3, 25)
      fit = fitnessAutomata(nfaResultado, test_csv, sRet, sRetTest=False)
      bpmn = nfaBB_to_bpmn(nfaResultado)
      gateways, tasks, flows = countBPMN(bpmn)
      comparacaoBPMN.append(["Operação Sequencias min/max:3-25 estados DFA min join", gateways, tasks, flows, gateways+tasks, fit])
    

  elif camMin:
    if sRet:
      nfaCamMin = to_nfa_minimum_path(train_csv, rework=False, nfa_bb=False)

      

      dfa = nfaCamMin.determinization()
      


      min = dfa.minimization()
      


      min = dfaToNfa(min)
      nfaResultado = operacaoSequencias(min, 3, 25)
      fit = fitnessAutomata(nfaResultado, test_csv, sRet, sRetTest=False)
      bpmn = nfaBB_to_bpmn(nfaResultado)
      gateways, tasks, flows = countBPMN(bpmn)
      comparacaoBPMN.append(["Operação Sequencias min/max:3-25 estados DFA min caminhos mínimos s retrabalho", gateways, tasks, flows, gateways+tasks, fit])  

    else:
      nfaCamMin = to_nfa_minimum_path(train_csv, nfa_bb=False)

      

      dfa = nfaCamMin.determinization()
      


      min = dfa.minimization()
      


      min = dfaToNfa(min)
      nfaResultado = operacaoSequencias(min, 3, 25)
      fit = fitnessAutomata(nfaResultado, test_csv, sRet, sRetTest=False)
      bpmn = nfaBB_to_bpmn(nfaResultado)
      gateways, tasks, flows = countBPMN(bpmn)
      comparacaoBPMN.append(["Operação Sequencias min/max:3-25 estados DFA min caminhos mínimos", gateways, tasks, flows, gateways+tasks, fit])  

  else: 
    nfa = to_nfa(train_csv)

    

    dfa = nfa.determinization()
    


    min = dfa.minimization()
    


    min = dfaToNfa(min)
    nfaResultado = operacaoSequencias(min, 3, 25)
    fit = fitnessAutomata(nfaResultado, test_csv, sRet, sRetTest=False)
    bpmn = nfaBB_to_bpmn(nfaResultado)
    gateways, tasks, flows = countBPMN(bpmn)
    comparacaoBPMN.append(["Operação Sequencias min/max:3-25 estados DFA min caminhos mínimos", gateways, tasks, flows, gateways+tasks, fit])  



  outBPMN = widgets.Output()
  tabsBPMN = widgets.Tab(children=[outBPMN])
  tabsBPMN.set_title(0, 'BPMN')
  display(tabsBPMN)
  with outBPMN:
    text = "Tam log: " + str(len(train_csv))
    sum = 0
    for x in train_csv:
      sum+=len(x)
    textSum = "N° eventos: " + str(sum)


    display(text)


    display(textSum)

    display(pd.DataFrame(comparacaoBPMN,columns=["Referente à:", "Gateways","Tasks","Transições","Componentes", "Acurácia"]))
