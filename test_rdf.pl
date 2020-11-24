:- use_module(library(lists)).
:- use_module(library(rdf)).

:- [rdfs].

load_aat_rdf :-
    load_rdf_file('/home/janw/src/eculture/RDF/vocabularies/getty/aat.rdf').
load_aat_rdfs :-
    load_rdf_file('/home/janw/src/eculture/RDF/vocabularies/getty/aat.rdfs').

load_rdf_file(File) :-
    load_rdf(File, Triples),
    time(forall(member(rdf(S,P,O), Triples), rdf_assert(S,P,O))).
