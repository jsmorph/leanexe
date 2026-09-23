namespace LeanExe.Wasi

abbrev Action (α : Type) := BaseIO α

structure FdStat where
  filetype : UInt32
  flags : UInt32
  rightsBase : UInt64
  rightsInheriting : UInt64

structure FileStat where
  device : UInt64
  inode : UInt64
  filetype : UInt32
  nlink : UInt64
  size : UInt64
  atim : UInt64
  mtim : UInt64
  ctim : UInt64

structure Prestat where
  tag : UInt32
  nameLength : UInt32

structure Subscription where
  userdata : UInt64
  eventType : UInt32
  id : UInt32
  timeout : UInt64
  precision : UInt64
  flags : UInt32

def Subscription.clock (userdata : UInt64) (id : UInt32)
    (timeout precision : UInt64) (flags : UInt32) : Subscription :=
  ⟨userdata, 0, id, timeout, precision, flags⟩

def Subscription.read (userdata : UInt64) (fd : UInt32) : Subscription :=
  ⟨userdata, 1, fd, 0, 0, 0⟩

def Subscription.write (userdata : UInt64) (fd : UInt32) : Subscription :=
  ⟨userdata, 2, fd, 0, 0, 0⟩

structure Event where
  userdata : UInt64
  error : UInt32
  eventType : UInt32
  nbytes : UInt64
  flags : UInt32

namespace Errno

def success : UInt32 := 0
def «2big» : UInt32 := 1
def acces : UInt32 := 2
def addrinuse : UInt32 := 3
def addrnotavail : UInt32 := 4
def afnosupport : UInt32 := 5
def again : UInt32 := 6
def already : UInt32 := 7
def badf : UInt32 := 8
def badmsg : UInt32 := 9
def busy : UInt32 := 10
def canceled : UInt32 := 11
def child : UInt32 := 12
def connaborted : UInt32 := 13
def connrefused : UInt32 := 14
def connreset : UInt32 := 15
def deadlk : UInt32 := 16
def destaddrreq : UInt32 := 17
def dom : UInt32 := 18
def dquot : UInt32 := 19
def exist : UInt32 := 20
def fault : UInt32 := 21
def fbig : UInt32 := 22
def hostunreach : UInt32 := 23
def idrm : UInt32 := 24
def ilseq : UInt32 := 25
def inprogress : UInt32 := 26
def intr : UInt32 := 27
def inval : UInt32 := 28
def io : UInt32 := 29
def isconn : UInt32 := 30
def isdir : UInt32 := 31
def loop : UInt32 := 32
def mfile : UInt32 := 33
def mlink : UInt32 := 34
def msgsize : UInt32 := 35
def multihop : UInt32 := 36
def nametoolong : UInt32 := 37
def netdown : UInt32 := 38
def netreset : UInt32 := 39
def netunreach : UInt32 := 40
def nfile : UInt32 := 41
def nobufs : UInt32 := 42
def nodev : UInt32 := 43
def noent : UInt32 := 44
def noexec : UInt32 := 45
def nolck : UInt32 := 46
def nolink : UInt32 := 47
def nomem : UInt32 := 48
def nomsg : UInt32 := 49
def noprotoopt : UInt32 := 50
def nospc : UInt32 := 51
def nosys : UInt32 := 52
def notconn : UInt32 := 53
def notdir : UInt32 := 54
def notempty : UInt32 := 55
def notrecoverable : UInt32 := 56
def notsock : UInt32 := 57
def notsup : UInt32 := 58
def notty : UInt32 := 59
def nxio : UInt32 := 60
def overflow : UInt32 := 61
def ownerdead : UInt32 := 62
def perm : UInt32 := 63
def pipe : UInt32 := 64
def proto : UInt32 := 65
def protonosupport : UInt32 := 66
def prototype : UInt32 := 67
def range : UInt32 := 68
def rofs : UInt32 := 69
def spipe : UInt32 := 70
def srch : UInt32 := 71
def stale : UInt32 := 72
def timedout : UInt32 := 73
def txtbsy : UInt32 := 74
def xdev : UInt32 := 75
def notcapable : UInt32 := 76

end Errno

namespace Clock

def realtime : UInt32 := 0
def monotonic : UInt32 := 1
def process_cputime_id : UInt32 := 2
def thread_cputime_id : UInt32 := 3

end Clock

namespace Rights

def fd_datasync : UInt64 := 1
def fd_read : UInt64 := 2
def fd_seek : UInt64 := 4
def fd_fdstat_set_flags : UInt64 := 8
def fd_sync : UInt64 := 16
def fd_tell : UInt64 := 32
def fd_write : UInt64 := 64
def fd_advise : UInt64 := 128
def fd_allocate : UInt64 := 256
def path_create_directory : UInt64 := 512
def path_create_file : UInt64 := 1024
def path_link_source : UInt64 := 2048
def path_link_target : UInt64 := 4096
def path_open : UInt64 := 8192
def fd_readdir : UInt64 := 16384
def path_readlink : UInt64 := 32768
def path_rename_source : UInt64 := 65536
def path_rename_target : UInt64 := 131072
def path_filestat_get : UInt64 := 262144
def path_filestat_set_size : UInt64 := 524288
def path_filestat_set_times : UInt64 := 1048576
def fd_filestat_get : UInt64 := 2097152
def fd_filestat_set_size : UInt64 := 4194304
def fd_filestat_set_times : UInt64 := 8388608
def path_symlink : UInt64 := 16777216
def path_remove_directory : UInt64 := 33554432
def path_unlink_file : UInt64 := 67108864
def poll_fd_readwrite : UInt64 := 134217728
def sock_shutdown : UInt64 := 268435456
def sock_accept : UInt64 := 536870912

end Rights

namespace Whence

def set : UInt32 := 0
def cur : UInt32 := 1
def «end» : UInt32 := 2

end Whence

namespace Filetype

def unknown : UInt32 := 0
def block_device : UInt32 := 1
def character_device : UInt32 := 2
def directory : UInt32 := 3
def regular_file : UInt32 := 4
def socket_dgram : UInt32 := 5
def socket_stream : UInt32 := 6
def symbolic_link : UInt32 := 7

end Filetype

namespace Advice

def normal : UInt32 := 0
def sequential : UInt32 := 1
def random : UInt32 := 2
def willneed : UInt32 := 3
def dontneed : UInt32 := 4
def noreuse : UInt32 := 5

end Advice

namespace Fdflags

def append : UInt32 := 1
def dsync : UInt32 := 2
def nonblock : UInt32 := 4
def rsync : UInt32 := 8
def sync : UInt32 := 16

end Fdflags

namespace Fstflags

def atim : UInt32 := 1
def atim_now : UInt32 := 2
def mtim : UInt32 := 4
def mtim_now : UInt32 := 8

end Fstflags

namespace Lookupflags

def symlink_follow : UInt32 := 1

end Lookupflags

namespace Oflags

def creat : UInt32 := 1
def directory : UInt32 := 2
def excl : UInt32 := 4
def trunc : UInt32 := 8

end Oflags

namespace Eventtype

def clock : UInt32 := 0
def fd_read : UInt32 := 1
def fd_write : UInt32 := 2

end Eventtype

namespace Eventrwflags

def fd_readwrite_hangup : UInt32 := 1

end Eventrwflags

namespace Subclockflags

def subscription_clock_abstime : UInt32 := 1

end Subclockflags

namespace Signal

def none : UInt32 := 0
def hup : UInt32 := 1
def int : UInt32 := 2
def quit : UInt32 := 3
def ill : UInt32 := 4
def trap : UInt32 := 5
def abrt : UInt32 := 6
def bus : UInt32 := 7
def fpe : UInt32 := 8
def kill : UInt32 := 9
def usr1 : UInt32 := 10
def segv : UInt32 := 11
def usr2 : UInt32 := 12
def pipe : UInt32 := 13
def alrm : UInt32 := 14
def term : UInt32 := 15
def chld : UInt32 := 16
def cont : UInt32 := 17
def stop : UInt32 := 18
def tstp : UInt32 := 19
def ttin : UInt32 := 20
def ttou : UInt32 := 21
def urg : UInt32 := 22
def xcpu : UInt32 := 23
def xfsz : UInt32 := 24
def vtalrm : UInt32 := 25
def prof : UInt32 := 26
def winch : UInt32 := 27
def poll : UInt32 := 28
def pwr : UInt32 := 29
def sys : UInt32 := 30

end Signal

namespace Riflags

def recv_peek : UInt32 := 1
def recv_waitall : UInt32 := 2

end Riflags

namespace Roflags

def recv_data_truncated : UInt32 := 1

end Roflags

namespace Siflags


end Siflags

namespace Sdflags

def rd : UInt32 := 1
def wr : UInt32 := 2

end Sdflags

@[extern "leanexe_wasi_args_get"]
opaque args_get : Action (Except UInt32 (Array ByteArray))

@[extern "leanexe_wasi_args_sizes_get"]
opaque args_sizes_get : Action (Except UInt32 (UInt32 × UInt32))

@[extern "leanexe_wasi_environ_get"]
opaque environ_get : Action (Except UInt32 (Array ByteArray))

@[extern "leanexe_wasi_environ_sizes_get"]
opaque environ_sizes_get : Action (Except UInt32 (UInt32 × UInt32))

@[extern "leanexe_wasi_clock_res_get"]
opaque clock_res_get (id : UInt32) : Action (Except UInt32 UInt64)

@[extern "leanexe_wasi_clock_time_get"]
opaque clock_time_get (id : UInt32) (precision : UInt64) : Action (Except UInt32 UInt64)

@[extern "leanexe_wasi_fd_advise"]
opaque fd_advise (fd : UInt32) (offset : UInt64) (len : UInt64) (advice : UInt32) : Action UInt32

@[extern "leanexe_wasi_fd_allocate"]
opaque fd_allocate (fd : UInt32) (offset : UInt64) (len : UInt64) : Action UInt32

@[extern "leanexe_wasi_fd_close"]
opaque fd_close (fd : UInt32) : Action UInt32

@[extern "leanexe_wasi_fd_datasync"]
opaque fd_datasync (fd : UInt32) : Action UInt32

@[extern "leanexe_wasi_fd_fdstat_get"]
opaque fd_fdstat_get (fd : UInt32) : Action (Except UInt32 FdStat)

@[extern "leanexe_wasi_fd_fdstat_set_flags"]
opaque fd_fdstat_set_flags (fd : UInt32) (flags : UInt32) : Action UInt32

@[extern "leanexe_wasi_fd_fdstat_set_rights"]
opaque fd_fdstat_set_rights (fd : UInt32) (rightsBase : UInt64) (rightsInheriting : UInt64) : Action UInt32

@[extern "leanexe_wasi_fd_filestat_get"]
opaque fd_filestat_get (fd : UInt32) : Action (Except UInt32 FileStat)

@[extern "leanexe_wasi_fd_filestat_set_size"]
opaque fd_filestat_set_size (fd : UInt32) (size : UInt64) : Action UInt32

@[extern "leanexe_wasi_fd_filestat_set_times"]
opaque fd_filestat_set_times (fd : UInt32) (atim : UInt64) (mtim : UInt64) (flags : UInt32) : Action UInt32

@[extern "leanexe_wasi_fd_pread"]
opaque fd_pread (fd : UInt32) (maxBytes : UInt32) (offset : UInt64) : Action (Except UInt32 ByteArray)

@[extern "leanexe_wasi_fd_prestat_get"]
opaque fd_prestat_get (fd : UInt32) : Action (Except UInt32 Prestat)

@[extern "leanexe_wasi_fd_prestat_dir_name"]
opaque fd_prestat_dir_name (fd : UInt32) (nameLength : UInt32) : Action (Except UInt32 ByteArray)

@[extern "leanexe_wasi_fd_pwrite"]
opaque fd_pwrite (fd : UInt32) (bytes : ByteArray) (offset : UInt64) : Action (Except UInt32 UInt32)

@[extern "leanexe_wasi_fd_read"]
opaque fd_read (fd : UInt32) (maxBytes : UInt32) : Action (Except UInt32 ByteArray)

@[extern "leanexe_wasi_fd_readdir"]
opaque fd_readdir (fd : UInt32) (maxBytes : UInt32) (cookie : UInt64) : Action (Except UInt32 ByteArray)

@[extern "leanexe_wasi_fd_renumber"]
opaque fd_renumber (fd : UInt32) (to : UInt32) : Action UInt32

@[extern "leanexe_wasi_fd_seek"]
opaque fd_seek (fd : UInt32) (offset : UInt64) (whence : UInt32) : Action (Except UInt32 UInt64)

@[extern "leanexe_wasi_fd_sync"]
opaque fd_sync (fd : UInt32) : Action UInt32

@[extern "leanexe_wasi_fd_tell"]
opaque fd_tell (fd : UInt32) : Action (Except UInt32 UInt64)

@[extern "leanexe_wasi_fd_write"]
opaque fd_write (fd : UInt32) (bytes : ByteArray) : Action (Except UInt32 UInt32)

@[extern "leanexe_wasi_path_create_directory"]
opaque path_create_directory (fd : UInt32) (path : ByteArray) : Action UInt32

@[extern "leanexe_wasi_path_filestat_get"]
opaque path_filestat_get (fd : UInt32) (flags : UInt32) (path : ByteArray) : Action (Except UInt32 FileStat)

@[extern "leanexe_wasi_path_filestat_set_times"]
opaque path_filestat_set_times (fd : UInt32) (flags : UInt32) (path : ByteArray) (atim : UInt64) (mtim : UInt64) (fstflags : UInt32) : Action UInt32

@[extern "leanexe_wasi_path_link"]
opaque path_link (oldFd : UInt32) (oldFlags : UInt32) (oldPath : ByteArray) (newFd : UInt32) (newPath : ByteArray) : Action UInt32

@[extern "leanexe_wasi_path_open"]
opaque path_open (fd : UInt32) (dirflags : UInt32) (path : ByteArray) (oflags : UInt32) (rightsBase : UInt64) (rightsInheriting : UInt64) (fdflags : UInt32) : Action (Except UInt32 UInt32)

@[extern "leanexe_wasi_path_readlink"]
opaque path_readlink (fd : UInt32) (path : ByteArray) (maxBytes : UInt32) : Action (Except UInt32 ByteArray)

@[extern "leanexe_wasi_path_remove_directory"]
opaque path_remove_directory (fd : UInt32) (path : ByteArray) : Action UInt32

@[extern "leanexe_wasi_path_rename"]
opaque path_rename (fd : UInt32) (oldPath : ByteArray) (newFd : UInt32) (newPath : ByteArray) : Action UInt32

@[extern "leanexe_wasi_path_symlink"]
opaque path_symlink (oldPath : ByteArray) (fd : UInt32) (newPath : ByteArray) : Action UInt32

@[extern "leanexe_wasi_path_unlink_file"]
opaque path_unlink_file (fd : UInt32) (path : ByteArray) : Action UInt32

@[extern "leanexe_wasi_poll_oneoff"]
opaque poll_oneoff (subscriptions : Array Subscription) : Action (Except UInt32 (Array Event))

@[extern "leanexe_wasi_proc_exit"]
opaque proc_exit (code : UInt32) : Action Unit

@[extern "leanexe_wasi_proc_raise"]
opaque proc_raise (signal : UInt32) : Action UInt32

@[extern "leanexe_wasi_sched_yield"]
opaque sched_yield : Action UInt32

@[extern "leanexe_wasi_random_get"]
opaque random_get (size : UInt32) : Action (Except UInt32 ByteArray)

@[extern "leanexe_wasi_sock_accept"]
opaque sock_accept (fd : UInt32) (flags : UInt32) : Action (Except UInt32 UInt32)

@[extern "leanexe_wasi_sock_recv"]
opaque sock_recv (fd : UInt32) (maxBytes : UInt32) (flags : UInt32) : Action (Except UInt32 (ByteArray × UInt32))

@[extern "leanexe_wasi_sock_send"]
opaque sock_send (fd : UInt32) (bytes : ByteArray) (flags : UInt32) : Action (Except UInt32 UInt32)

@[extern "leanexe_wasi_sock_shutdown"]
opaque sock_shutdown (fd : UInt32) (how : UInt32) : Action UInt32

end LeanExe.Wasi
