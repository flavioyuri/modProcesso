from setuptools import setup

with open('README.md', 'r') as arq:
  readme = arq.read()

setup(
    name='modProcesso',
    version='0.0.10',
    license='MIT',
    author="Flávio Yuri de Sousa",
    author_email='flavioyuri22@gmail.com',
    packages=['modProcesso'],
    url='https://github.com/flavioyuri/modProcesso',
    description='''modProcesso is a library for automata modularisation.''',
    long_description=readme,
    long_description_content_type='text/markdown',
    keywords='Theory of Computing, Automata Theory, Languages, Process Mining, Automata Decomposition, Process Modularisation', 
    install_requires=[
        'teocomp',
        'pm4py',
        'ipywidgets',
        'automaton2bpmn', 
      ],

)