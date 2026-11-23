# Structural Unfaithfulness
The same logical structure up to the NL.

For example, if NL is $P \land Q$, then formalizm needs the $\land$ so something like $a=b \land (c>d \land q)$ works. but simply $a=b$ does not. 

## caveat
sometimes a function maybe is like $e(s)$ for NL where it is the $s$'s basis of standard basis thing, but in lean it may have two inputs rather than one something like $e(s, 1)$ to denote [0, 0, 1, 0] rather than [0, 0, 2, 0] which would be represented $e(s,2)$