.PHONY: FORCE

blake2s.sum: FORCE spark.smf
	@spark @spark.smf
	@sparksimp
	@isabelle build -D . -e
	@pogs

adactl: FORCE blake2sn.aru
	@for i in bin/*.adb; do \
		gnatmake -Icommon -Igeneric -gnat95 -gnatk8 -gnatct -q $${i}; \
		adactl -e -f blake2sn.aru -r \
		  $$(echo $${i} | sed -e 's:.*/::' -e 's:.ad[bs]:.adt:'); \
	done
	@echo "Passed AdaControl"
	-@rm -f *.adt *.ali

adactl.old: FORCE blake2so.aru
	@for i in bin/*.adb; do \
		gnatmake -Icommon -Igeneric -gnat95 -gnatk8 -gnatct -q $${i}; \
		adactl -e -f blake2so.aru -r \
		  $$(echo $${i} | sed -e 's:.*/::' -e 's:.ad[bs]:.adt:'); \
	done
	@echo "Passed AdaControl"
	-@rm -f *.adt *.ali

clean: FORCE
	-@rm -f b2stest/parse_file/*.prv blake2s/*.prv quadlets/*.prv
	-@sparkclean -examiner -simplifier
	-@rm -f *~ *.adt *.ali *.lst *.o *.rep *.sli *.stderr *.stdout
