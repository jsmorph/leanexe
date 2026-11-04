# The QEMU runs of tests/baremetal/run.sh, programs.sh, inputs.sh, and ctl.sh, which source this
# file.
# ACCEL selects the accelerator: tcg, the default, or kvm.  Under TCG, QEMU emulates a
# Cortex-A57 and the startup code exits through semihosting, so QEMU's exit status is the
# program's.  Under KVM, the guest runs on the host's AArch64 CPU, where semihosting is
# unavailable, so bm_defines holds -DPSCI_EXIT for tools/baremetal/build.sh: the startup code
# turns the machine off through PSCI SYSTEM_OFF after its report, QEMU must exit with status 0,
# and the program's status is the one that the report gives, N for "R:exit N", 255 for
# "R:exception", and 254 for "R:level".  QEMU names qemu-system-aarch64.
accel=${ACCEL:-tcg}
qemu=${QEMU:-qemu-system-aarch64}
case "$accel" in
  tcg)
    bm_cpu=(-cpu cortex-a57)
    bm_semihosting=(-semihosting-config enable=on,target=native)
    bm_defines=()
    ;;
  kvm)
    bm_cpu=(-accel kvm -cpu host)
    bm_semihosting=()
    bm_defines=(-DPSCI_EXIT)
    ;;
  *)
    echo "ACCEL must be tcg or kvm, not $accel" >&2
    exit 2
    ;;
esac

# Runs the image $3 on the machine $1 with its UART output in the file $2 and the QEMU options
# after $3, within TIMEOUT seconds, 120 unless set, and sets code to the program's exit status,
# or to "qemu N" when QEMU under KVM exits with status N.  The report is the last line of the
# output, after any bytes of the program's.
bm_run() {
  local machine=$1 serial=$2 image=$3 qcode=0
  shift 3
  rm -f "$serial"
  timeout "${TIMEOUT:-120}" "$qemu" -M "$machine" "${bm_cpu[@]}" -m 1G -display none \
    -monitor none -serial "file:$serial" "${bm_semihosting[@]}" "$@" -kernel "$image" \
    </dev/null || qcode=$?
  if [ "$accel" = tcg ]; then
    code=$qcode
  elif [ "$qcode" -ne 0 ]; then
    code="qemu $qcode"
  else
    code=$(tail -n 1 "$serial" | LC_ALL=C sed -n \
      -e 's/^.*R:exit \([0-9]*\) el [0-9]* stack [0-9]*$/\1/p' \
      -e 's/^.*R:exception [0-9]* esr 0x[0-9a-f]* elr 0x[0-9a-f]* far 0x[0-9a-f]*$/255/p' \
      -e 's/^.*R:level [0-9]*$/254/p')
    code=${code:-none}
  fi
}

# Runs the image $3 on the machine $1 with the QEMU options after $4, as bm_run does, for a
# program that never ends: it copies the first $4 bytes of the UART output to the file $2 and
# then stops QEMU with SIGTERM, unless QEMU has exited.  When QEMU exits, or TIMEOUT seconds
# pass, before the output reaches $4 bytes, the file holds the output up to then.  code is
# QEMU's exit status, 0 after the stop and 124 after the timeout.  QEMU writes the UART output
# to its standard output, a FIFO that the shell opens before QEMU starts, so that head reaches
# the end of the FIFO even when QEMU exits before it opens the serial port.
bm_stream() {
  local machine=$1 serial=$2 image=$3 bytes=$4 fifo=$2.fifo pid
  shift 4
  rm -f "$serial" "$fifo"
  mkfifo "$fifo"
  timeout "${TIMEOUT:-120}" "$qemu" -M "$machine" "${bm_cpu[@]}" -m 1G -display none \
    -monitor none -serial stdio "${bm_semihosting[@]}" "$@" -kernel "$image" \
    </dev/null >"$fifo" &
  pid=$!
  head -c "$bytes" "$fifo" >"$serial"
  rm "$fifo"
  kill "$pid" 2>/dev/null || :
  code=0
  wait "$pid" || code=$?
}
