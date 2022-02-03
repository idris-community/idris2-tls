include config.mk

IDRIS := idris2
INSTALLDIR = `${IDRIS} --libdir`/tls-0.0.1/lib

TARGET = libidristls

ifeq ($(OS), windows)
	LDFLAGS += -lbcrypt
endif

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)

all: $(TARGET)$(SHLIB_SUFFIX)

$(TARGET)$(SHLIB_SUFFIX): $(OBJS)
	$(CC) -shared -o $@ $^ $(LDFLAGS)

-include $(DEPS)

.PHONY: clean
clean :
	rm -f $(OBJS) $(TARGET)$(SHLIB_SUFFIX)

cleandep: clean
	rm -f $(DEPS)

.PHONY: install
install:
	@if ! [ -d $(INSTALLDIR) ]; then mkdir -p $(INSTALLDIR); fi
	echo $(INSTALLDIR)
	install $(TARGET)$(SHLIB_SUFFIX) $(wildcard *.h) $(INSTALLDIR)
