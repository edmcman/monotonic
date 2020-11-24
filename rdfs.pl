rdfs(P, rdf:type, rdf:'Property') :-                            % rdf1
    rdfs(_, P, _).
rdfs(X, rdf:type, C) :-                                         % rdfs2
    rdfs(P, rdfs:domain, C),
    rdfs(X, P, _).
rdfs(Y, rdf:type, C) :-						% rdfs3
    rdfs(P, rdfs:range, C),
    rdfs(_, P, Y).
rdfs(X, rdf:type, rdfs:'Resource') :-				% rdfs4a
    rdfs(X, _, _).
rdfs(Y, rdf:type, rdfs:'Resource') :-                           % rdfs4b
    rdfs(_, _, Y).
rdfs(P, rdfs:subPropertyOf, R) :-				% rdfs5
    rdfs(P, rdfs:subPropertyOf, Q),
    rdfs(Q, rdfs:subPropertyOf, R).
rdfs(P, rdfs:subPropertyOf, P) :-				% rdfs6
    rdfs(P, rdf:type, rdf:'Property').
rdfs(X, Q, Y) :-						% rdfs7
    rdfs(P, rdfs:subPropertyOf, Q),
    rdfs(X, P, Y).
rdfs(C, rdfs:subClassOf, rdfs:'Resource') :-			% rdfs8
    rdfs(C, rdf:type, rdfs:'Class').
rdfs(X, rdf:type, D) :-						% rdfs9
    rdfs(C, rdfs:subClassOf, D),
    rdfs(X, rdf:type, C).
rdfs(C, rdfs:subClassOf, C) :-					% rdfs10
    rdfs(C, rdf:type, rdfs:'Class').
rdfs(C, rdfs:subClassOf, E) :-					% rdfs11
    rdfs(C, rdfs:subClassOf, D),
    rdfs(D, rdfs:subClassOf, E).
rdfs(P, rdfs:subPropertyOf, rdfs:member) :-                     % rdfs12
    rdfs(P, rdf:type, rdfs:'ContainerMembershipProperty').
rdfs(X, rdfs:subClassOf, rdfs:'Literal') :-                     % rdfs13
    rdfs(X, rdf:type, rdfs:'Datatype').
