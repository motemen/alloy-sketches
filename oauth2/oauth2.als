open util/ordering[Time]

sig Time {}

sig AuthorizationServer {
    knownClients:        ClientId one -> one Client,
    knownResourceOwners: UserAgent -> lone ResourceOwner,
    issuedCodes:         (Code -> lone Client -> ResourceOwner) -> Time,
}

sig Client {
    id:                     disj ClientId,
    secret:                 disj ClientSecret,
    userAgentStates:        (State lone -> lone UserAgent) -> Time,
    obtainedAuthorizations: (UserAgent -> lone ResourceOwner) -> Time,
}

fun authServer(client: Client): one AuthorizationServer {
    { authServer: AuthorizationServer | authServer.knownClients[client.id] = client }
}

fun authorizedResource(authServer: AuthorizationServer, code: Code, clientId: ClientId, clientSecret: ClientSecret, t: Time): lone ResourceOwner {
    {
        resourceOwner: ResourceOwner | let client = authServer.knownClients[clientId] {
            client.secret = clientSecret
            code -> client -> resourceOwner in authServer.issuedCodes.t
        }
    }
}

sig ResourceOwner {}

abstract sig Token {}
sig ClientId, ClientSecret, Code, State extends Token {}

abstract sig UserAgent {}
sig InnocentUserAgent, MaliciousUserAgent extends UserAgent {}

abstract sig Event {
    pre, post: Time,
    userAgent: UserAgent,
    inParams:  set Token,
    outParams: set Token,
    initiator: lone Event,
}

sig UserAgentVisitsClientEvent extends Event {
    client: Client,
    state:  disj State,
} {
    no initiator
    inParams  = none
    outParams = state + client.id

    userAgentStates.post = userAgentStates.pre + client -> state -> userAgent
}

sig AuthorizationServerIssueCodeEvent extends Event {
    authServer:    AuthorizationServer,
    code:          disj Code,
    resourceOwner: ResourceOwner,
    clientId:      ClientId,
    state:         State,
} {
    initiator in UserAgentVisitsClientEvent
    inParams  = clientId + state
    outParams = code + state

    let client = authServer.knownClients[clientId] {
        authServer -> code -> client -> resourceOwner not in issuedCodes.pre
        resourceOwner = authServer.knownResourceOwners[userAgent]
        issuedCodes.post = issuedCodes.pre + authServer -> code -> client -> resourceOwner
    }
}

sig ClientAuthorizesUserAgentEvent extends Event {
    client: Client,
    code:   Code,
    state:  State,
} {
    initiator in AuthorizationServerIssueCodeEvent
    inParams  = code + state
    outParams = none

    client -> state -> userAgent in userAgentStates.pre

    let resourceOwner = client.authServer.authorizedResource[code, client.id, client.secret, pre] {
        some resourceOwner
        client -> userAgent -> resourceOwner not in obtainedAuthorizations.pre
        obtainedAuthorizations.post = obtainedAuthorizations.pre + client -> userAgent -> resourceOwner
    }
}

fact eventsTakeOverInitiatorsParams {
    all e: Event {
        let e' = e.initiator {
            e.inParams = e'.outParams
            some e' implies { e.userAgent = e'.userAgent or e'.userAgent in MaliciousUserAgent }
        }
    }
}

pred init(t: Time) {
    no issuedCodes.t
    no obtainedAuthorizations.t
    no userAgentStates.t
}

pred step(t, t': Time) {
    some e: Event {
        e.pre  = t
        e.post = t'

        userAgentStates.t        != userAgentStates.t'        iff e in UserAgentVisitsClientEvent
        issuedCodes.t            != issuedCodes.t'            iff e in AuthorizationServerIssueCodeEvent
        obtainedAuthorizations.t != obtainedAuthorizations.t' iff e in ClientAuthorizesUserAgentEvent
    }
}

fact trace {
    init[first]

    all t: Time, t': t.next {
        step[t, t']
    }
}

run show {} for 6 but 1 AuthorizationServer, 1 Client

pred allUserAgentsAreEventuallyAuthorized {
    #InnocentUserAgent > 0

    all userAgent: InnocentUserAgent {
        some client: Client, t: Time {
            some client.obtainedAuthorizations.t[userAgent]
        }
    }
}

run allUserAgentsAreEventuallyAuthorized for 6 but exactly 1 AuthorizationServer, exactly 1 Client, 2 UserAgent

assert userAgentsAreProperlyAuthorized {
    all client: Client, userAgent: InnocentUserAgent, resourceOwner: ResourceOwner, t: Time {
        resourceOwner in client.obtainedAuthorizations.t[userAgent] implies {
            let authServer = client.authServer {
                authServer.knownResourceOwners[userAgent] = resourceOwner
                client -> resourceOwner in authServer.issuedCodes.t[Code]
            }
        }
    }
}

check userAgentsAreProperlyAuthorized for 6 but exactly 1 AuthorizationServer, exactly 1 Client, 2 UserAgent
