--------------------------- MODULE CRImplSS ---------------------------------
EXTENDS MCCR

val_bar == srvVals[TAIL]
accepted_bar == srvReplied[TAIL]

SS == INSTANCE SS WITH
    val <- val_bar,
    accepted <- accepted_bar

SSSpec == SS!SSSpec

=============================================================================