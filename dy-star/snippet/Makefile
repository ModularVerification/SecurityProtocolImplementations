include ../Makefile

APP_BASE_FST_FILES=RecvSentMsgDefinitions.fst
APP_BASE_CMX_FILES=ocaml-symbolic/RecvSentMsgDefinitions.cmx

APP_FST_FILES=RecvSentMsg.fst
APP_CMX_FILES=ocaml-symbolic/RecvSentMsg.cmx

ALL_FST_FILES=$(LIB_BASE_FST_FILES) $(APP_BASE_FST_FILES) $(LIB_FST_FILES) $(APP_FST_FILES)
ALL_CMX_FILES=$(LIB_BASE_CMX_FILES) $(APP_BASE_CMX_FILES) $(LIB_CMX_FILES) $(APP_CMX_FILES)

extract: $(ALL_FST_FILES) $(ALL_CMX_FILES)
test: $(ALL_FST_FILES) $(ALL_CMX_FILES) ocaml-symbolic/test.exe

ocaml-symbolic/test.exe: $(ALL_CMX_FILES)
	$(OCAMLOPT) $^ -o $@
