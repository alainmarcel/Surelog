TARGET           := lowrisc_systems_top_earlgrey_0.1
TOPLEVEL         := top_earlgrey
IVERILOG_OPTIONS := 

all: $(VPI_MODULES) $(TARGET)

$(TARGET):
	iverilog -s$(TOPLEVEL) -c $(TARGET).scr -o $@ $(IVERILOG_OPTIONS)

run: $(VPI_MODULES) $(TARGET)
	vvp -n -M. -l icarus.log $(patsubst %.vpi,-m%,$(VPI_MODULES)) $(TARGET) -fst $(EXTRA_OPTIONS)

clean:
	$(RM) $(VPI_MODULES) $(TARGET)
