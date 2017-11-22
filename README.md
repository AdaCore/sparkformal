# 1. Introduction

This project aims at developing a semantics of the SPARK language in Coq. It is
based on the Language Reference Manuals of
[Ada](http://www.ada-auth.org/standards/rm12_w_tc1/html/RM-TOC.html) and
[SPARK](http://docs.adacore.com/spark2014-docs/html/lrm/).

Initial work on that formalization was [published at HILT
2013](http://www.spark-2014.org/uploads/HILT2013_Presentation.pdf). Only a
small part of SPARK 2014 was formalized, but the architecture put in place
already allowed reading the abstract syntax tree produced by the GNAT compiler
frontend and checking that the equivalent generated abstract syntax tree in Coq
was well-formed and had the desired run-time checks.

The latest results were [published at SEFM
2017](http://www.spark-2014.org/uploads/sefm17-spark-formalization.pdf).

# 2. Goals

The SPARK toolset aims at giving guarantees to its users about the properties
of the software analyzed, be it absence of runtime errors or more complex
properties. But the SPARK toolset being itself a complex tool, it is not free
of errors. So how do we get confidence in the results of the analysis? The
established means for getting confidence in tools in industry in through a
process called sometimes tool certification, sometimes tool qualification. It
requires to describe at various levels of details (depending on the criticality
of the tool usage) the intended functionality of the tool, and to demonstrate
(usually through testing) that the tool correctly implements these
functionalities.

The academic way of obtaining confidence is also called "certification" but it
uncovers a completely different reality. It requires to provide mathematical
evidence, through mechanized proof, that the tool indeed performs a formally
specified functionality. Examples of that level of certification are the
CompCert compiler and the SEL4 operating system. This level of assurance is
very costly to achieve, and as a result not suitable for the majority of tools.

For SPARK, we have worked with our academic partners from Kansas State
University and Conservatoire National des Arts et Métiers to achieve a middle
ground, establishing mathematical evidence of the correctness of a critical
part of the SPARK toolset. The part on which we focused is the tagging of nodes
requiring run-time checks by the frontend of the SPARK technology. This
frontend is a critical and complex part, which is shared between the formal
verification tool GNATprove and the compiler GNAT. It is responsible for
generating semantically annotated Abstract Syntax Trees of the source code,
with special tags for nodes that require run-time checks. Then, GNATprove
relies on these tags to generate formulas to prove, so a missing tag means a
missing verification. Our interest in getting better assurance on this part of
the technology is not theoretical: that's a part where we repeatedly had errors
in the past, leading to missing verifications.

# 3. Contents

spark83_semantics - papers on earlier work on formalization of the previous
SPARK version, prior to SPARK 2014

spark2014_semantics - Coq formalization of a core of SPARK

papers - LaTeX sources for articles
