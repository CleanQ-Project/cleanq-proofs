# BSD 2-Clause License
# 
# Copyright (c) 2020, CleanQ Project - Systems Group, ETH Zurich
# All rights reserved.
# 
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# 
# 1. Redistributions of source code must retain the above copyright notice, this
#    list of conditions and the following disclaimer.
# 
# 2. Redistributions in binary form must reproduce the above copyright notice,
#    this list of conditions and the following disclaimer in the documentation
   # and/or other materials provided with the distribution.
# 
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


# the path to the Isabelle executable
ISABELLE=isabelle

# running isabelle with setting the L4V_ARCH variable
RUN_ISABELLE=L4V_ARCH=X64 $(ISABELLE) build -N -j 4

# the CleanQ sources directory
CLEANQ_DIR=CleanQ

# the CleanQ theory files 
CLEANQ_THEORIES=$(wildcard $(CLEANQ_DIR)/*.thy)

# additional dependencies for the documentation (root files)
CLEANQ_ROOT=$(CLEANQ_DIR)/ROOT $(CLEANQ_DIR)/root.tex


# 
# Build Targets
#

all: cleanq-proofs.pdf

<<<<<<< HEAD
# building the proofs and the documentation
cleanq-proofs.pdf: $(CLEANQ_THEORIES) $(CLEANQ_ROOT) Makefile deps
=======
cleanq-proofs.pdf: $(CLEANQ_THEORIES) $(CLEANQ_ROOT) Makefile
>>>>>>> bf659f8... omitting proofs from generated document
	$(RUN_ISABELLE) -D $(CLEANQ_DIR)
	cp build/cleanq/document.pdf  cleanq-proofs.pdf

clean :
	make -C doc clean


#
# Dependencies
#

deps: contrib/autocorres contrib/Simpl contrib/Complx

# autocorres dependency
contrib/autocorres:
	wget https://ts.data61.csiro.au/projects/TS/autocorres/autocorres-1.6.1.tar.gz
	tar -xf autocorres-1.6.1.tar.gz
	rm -rf autocorres-1.6.1.tar.gz
	mv autocorres-1.6.1 contrib/autocorres

# simpl dependency
contrib/Simpl: contrib/autocorres
	ln -s autocorres/c-parser/Simpl/ contrib/Simpl

# complex dependencies
contrib/Complx:
	wget https://www.isa-afp.org/release/afp-Complx-2019-06-11.tar.gz
	tar -xf afp-Complx-2019-06-11.tar.gz
	rm -rf afp-Complx-2019-06-11.tar.gz
	mv Complx contrib/Complx

