(*
  Igloo Case Study: Replication 
  Primary-Backup Replication

  $Id: Primary_Backup_1.thy 152658 2020-08-06 08:13:12Z tklenze $

  Author: Tobias Klenze <tobias.klenze@inf.ethz.ch>

  Date: December 2019
*)
chapter \<open>Igloo Case Study: Replication\<close>
text\<open>In this case study we model the protocol of a primary/backup replication system and its 
environmental assumptions as an event system, and show important invariants and trace properties.
Note that in contrast to other case studies, we have chosen to directly start with the concrete 
protocol rather than an abstract model.

The protocol is largely based on Chapter 2 (specifically, Sec 2.3.1) of the following book:
Replication. Theory and Practice. Bernadette Charron-Bost, Fernando Pedone, André Schiper. 
Springer 2010.

However, there are some minor modifications:
\begin{itemize}
\item The book is unclear how the primary server handles multiple pending requests by clients. It seems 
that the algorithm provided in their Fig. 2.4 does not allow handling multiple requests, and once 
the primary sends out a sync request to all backups, it has to wait for a reply from each one of them
before processing another client request. However, the description indicates that such concurrent 
processing should be possible. We thus amend the server's algorithm by additional state that is 
required to keep track of pending sync requests and pending client requests, allowing for the 
simultaneous processing of different client requests.
\item For simplicity, we use a single type variable 'uop (unique operation) instead of a tuple of 
unique identifier (uid) and operation. If needed, this can be instantiated as a tuple later on.
\item We send the unique operation along with the history in the primary's sync requests. This allows 
us to remove the other type of unique identifiers (uid2), since the uop uniquely identifies a 
primary's pending requests.
\item We include the history in the reply from the backup to the primary directly, rather than a unique
identifier (uid2) of it, or a hash of it. Such a unique identifier or hash could be added in a 
refinement step to minimize communication overhead and increase performance, however we currently do 
not do this optimization. Directly sending the history also allows us to have less state on the 
primary, as it does not need to keep track of pending sync requests (but it still has to keep track of 
pending client requests).
\end{itemize}

We now begin with the description of the protocol and our model.\<close>

section \<open>Primary-Backup Replication, Protocol Model\<close>

theory Primary_Backup_1
  imports
    Utils
begin

(**************************************************************************************************)
(**************************************************************************************************)
subsection \<open>System setup and Definitions\<close>
text\<open>The goal of the system is to create a distributed architecture which stores unique data values
in a fault-tolerant fashion.

The system contains two kinds of components, called agents:
\begin{itemize}
\item Clients, which generate unique operations (abstracted as type parameters 'uop) and request the
   distributed architecture to append them to the global history of uops.
\item Servers, which make up the distributed architecture. Servers store the global history of uops.
   They operate in one of two roles:
   (i) A primary server coordinates with all backup servers to make sure that the history is 
     synchronized between all living servers, 
   (ii) Any number of backup servers respond to sync requests by the primary server and are ready to 
     take over its role should it crash. There is a total order between server IDs which determines
     the next server to take over the role of the primary, should the current primary crash.
\end{itemize}

Servers can fail at any moment in a run of the protocol. The protocol ensures a consistent history 
is kept in the distributed system. The consistency condition is:
When a primary server replies to a client, then the history sent back to the client is a prefix of
the histories stored at all the servers. This is formalized as lemma @{term backup_consistency} below.

We assume the following crash-stop failure model:
\begin{itemize}
\item If there is a failure, it is eventually detected by each agent (Perfect Failure Detection).
\item Once a server has failed (it is not longer alive), it does not execute any events and it will 
   never become alive again.
\end{itemize}
\<close>

datatype agent = 
  Client cid |
  Server sid

text \<open>The global history of uops is just a list of them.\<close>
type_synonym 'uop history = "'uop list"

subsubsection \<open>Message Payloads and Channels\<close>
text \<open>Messages between clients and servers consists of update requests and update responses.\<close>
datatype 'uop m1_upd =
  m1_Upd_req "'uop" |
  m1_Upd_res "'uop" "'uop history"

instance m1_upd :: (countable) countable
  by countable_datatype

text \<open>Sync messages between servers:
The payload is the same in for requests and responses: the operation and the entire history is sent. This is
an abstraction over the protocol given in the replication book, in which the sync response does not 
contain the history, but rather a unique token (uid2) that ties a sync request and response to a 
particular history. Here, we include the history because it simplifies our proofs. However, a refined 
version could implement the protocol as specified in the book.\<close>
datatype 'uop m1_sync = 
  m1_Sync_req 'uop "'uop history" |  
  m1_Sync_res 'uop "'uop history"


text \<open>Buffers and channels are lists representing FIFOs, where new messages are appended at the 
end of the list. The environment assumption of FIFOs can be achieved by using an in-order transport
protocol such as TCP. The incoming and outgoing buffers ibuf and obuf are of the same type.\<close>
type_synonym 'uop m1_upd_fifo = "'uop m1_upd list"
type_synonym 'uop m1_sync_fifo = "'uop m1_sync list"


subsubsection \<open>State\<close>

record 'uop m1_state = 
  \<comment> \<open>client and server state\<close>
  live :: "agent \<Rightarrow> sid set" \<comment> \<open>servers' status as seen by each agent (Clients and Servers). The 
set is initialized with "sidset", a global parameter, which contains all initial servers' identifiers.
This set monotonically decreases throughout executions. Note that this state only captures the belief
of each agent of which server is alive -- it is an overapproximation of the set of servers that are
actually alive. The latter is given in the environment state elive below. For a server sid, sid is
contained in its liveset iff it is alive according to elive (we prove this as an invariant below).
Thus, whether a server is truly alive is stored redundantly in the server's own local state and in
the environment state.\<close>

  \<comment> \<open>client state\<close>
  cpend :: "cid \<Rightarrow> sid \<Rightarrow> 'uop \<Rightarrow> bool" \<comment> \<open>client's pending requests\<close>
  csobuf :: "cid \<Rightarrow> sid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>output buffer, messages from client to server\<close>
  scibuf :: "sid \<Rightarrow> cid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>input buffer, messages from server to client.\<close>

  \<comment> \<open>server state\<close>
  hist :: "sid \<Rightarrow> sid \<Rightarrow> 'uop history"         \<comment> \<open>server's histories. This is a history variable
and stores more than what would be stored on an actual system. The server's actual history is defined
as hist s sid sid. We use the other places of the hist variable for specification purposes:
for @{term "p < b"}: @{term "hist s b p"} is the latest history that backup b received from primary p as a sync request.
for @{term "p < b"}: @{term "hist s p b"} is the latest history that primary p received back from backup b as a sync reply.\<close>
  spend :: "sid \<Rightarrow> 'uop history"         \<comment> \<open>server's pending history, i.e., the extension of the 
current history (hist s sid sid) with operations that has not yet been confirmed by the clients.
It is only relevant for the primary server to keep track of pending changes, but gets overwritten 
by backup servers during syncs as well, since they could become primary servers at any moment.\<close>
  uopcid :: "sid \<Rightarrow> 'uop \<Rightarrow> cid option" \<comment> \<open>Stores the client ids for pending requests. Relevant only 
to primaries\<close>
  scobuf :: "sid \<Rightarrow> cid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>output buffer, messages from server to client.\<close>
  csibuf :: "cid \<Rightarrow> sid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>input buffer, messages from client to server.\<close>
  ssobuf :: "sid \<Rightarrow> sid \<Rightarrow> 'uop m1_sync_fifo" \<comment> \<open>output buffer, messages from server to server\<close>
  ssibuf :: "sid \<Rightarrow> sid \<Rightarrow> 'uop m1_sync_fifo" \<comment> \<open>input buffer, messages from server to server.\<close>

  \<comment> \<open>environment state\<close>
  cschan :: "cid \<Rightarrow> sid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>channel from client to server\<close>
  scchan :: "sid \<Rightarrow> cid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>channel from server to client\<close>
  sschan :: "sid \<Rightarrow> sid \<Rightarrow> 'uop m1_sync_fifo"       \<comment> \<open>channel from server to server\<close>
  uops :: "'uop set"      \<comment> \<open>used ids. Used to ensure freshness when drawing new unique operations.\<close>
  elive :: "sid set" \<comment> \<open>Set of nodes that are truly alive.\<close>

definition m1_init :: "sid set \<Rightarrow> 'uop m1_state \<Rightarrow> bool" where
  "m1_init sids s \<longleftrightarrow> s = \<lparr> 
    live = \<lambda>_. sids,           \<comment> \<open>initial set of servers. Given as a parameter to the model. 
Note that the set of server ids for some server includes his own id\<close>
    cpend = \<lambda>_ _ _ . False, 
    csobuf = \<lambda>_ _. [], 
    scibuf = \<lambda>_ _. [], 
    hist = \<lambda>_ _ . [], 
    spend = \<lambda>_ . [], 
    uopcid = \<lambda>_ _ . None, 
    scobuf = \<lambda>_ _. [], 
    csibuf = \<lambda>_ _. [], 
    ssobuf = \<lambda>_ _. [], 
    ssibuf = \<lambda>_ _. [], 
    cschan = \<lambda>_ _. [], 
    scchan = \<lambda>_ _. [], 
    sschan = \<lambda>_ _. [], 
    uops = {},
    elive = sids\<rparr>"

type_synonym 'uop m1_trans = "'uop m1_state \<Rightarrow> 'uop m1_state \<Rightarrow> bool"


subsubsection \<open>State changes\<close>
abbreviation app_msg where "app_msg s buf a b m \<equiv> fun_upd2 (buf s) a b ((buf s a b)@[m])"
abbreviation recv_msg where   "recv_msg s buf a b m \<equiv> is_head m (buf s a b)"
abbreviation rm_msg where     "rm_msg s buf a b \<equiv> fun_upd2 (buf s) a b (tl (buf s a b))"

abbreviation ss_app_msg where "ss_app_msg s buf a b m \<equiv> fun_upd2 (buf s) a b ((buf s a b)@[m])"
abbreviation ss_recv_msg where   "ss_recv_msg s buf a b m \<equiv> is_head m (buf s a b)"
abbreviation ss_rm_msg where     "ss_rm_msg s buf a b \<equiv> fun_upd2 (buf s) a b (tl (buf s a b))"

subsubsection \<open>Definitions on state\<close>
declare if_split_asm [split]

text \<open>Current suspected primary. This is only relevant for backup, as for primary it will be the own 
server ID. Returns an option, since the set of alive servers could be empty.\<close>
definition prim :: "'uop m1_state \<Rightarrow> agent \<Rightarrow> sid option" where 
  "prim s ag = least (live s ag)"

lemma primI:
  "\<lbrakk>sid \<in> live s ag; (\<And>sid' . sid' \<in> live s ag \<Longrightarrow> sid \<le> sid')\<rbrakk>\<Longrightarrow> prim s ag = Some sid"
  by(auto simp add: prim_def intro: LeastI dest: Least_le)(meson LeastI_ex Least_le eq_iff)

lemma primD: 
  "prim s ag = None \<Longrightarrow> live s ag = {}"
  "prim s ag = Some sid \<Longrightarrow> sid \<in> live s ag"
  "prim s ag = Some sid \<Longrightarrow> (\<And>sid' . sid' \<in> live s ag \<Longrightarrow> sid \<le> sid')"
    apply(auto simp add: prim_def intro: LeastI dest: Least_le)
    using Least_le by(fastforce)

lemma prim_id:
  "\<lbrakk>prim s' ag = Some p; live s' ag = live s ag\<rbrakk> \<Longrightarrow> prim s ag = Some p"
  by(auto simp add: prim_def)

lemma prim_eq:
  "\<lbrakk>live s' x = live s x\<rbrakk>  \<Longrightarrow> prim s' x = prim s x"
  by(auto simp add: prim_def)

text\<open>Because we assume perfect failure detection, if a single agent detects a failed server, 
     we know that server must have failed.
     A server is alive iff it believes itself to be alive. It can fail with the @{term m1_Detect_failure} 
     event, which ensures that the server first notices itself that it is dead.
     The information of which server is truly alive is also stored in the environment. The invariant
     @{term inv_elive} below shows that @{term "sid \<in> elive s"} iff @{term "alive s sid"}.\<close>
abbreviation alive :: "'uop m1_state \<Rightarrow> sid \<Rightarrow> bool" where
 "alive s sid \<equiv> sid \<in> live s (Server sid)"

text\<open>Returns the set of servers that are both believed by @{term "Server sid"} to be alive, and that are 
greater or equal to some given Server ID pr, which is the (believed) primary. In other words, if we
know that pr is (or was) the primary, then all servers with a smaller Server ID must have died.\<close>
definition live_geq where
  "live_geq s sid pr \<equiv> { x. x \<ge> pr \<and> x \<in> live s (Server sid)}"

text\<open>Definition used for @{term m1_C_req}\<close>
text\<open>Either generate a new request, or pick an existing request that has to be re-sent, because it
was sent to a primary that is no longer alive. If we know that the primary that we sent a request 
to has died, re-send the same request to the server that we currently believe is the primary.\<close>
definition cond_request where
  "cond_request s cid sid op is_resend \<equiv> (
    if is_resend 
    then (\<exists> sid'.
      cpend s cid sid' op \<and> \<comment> \<open>We already tried to send an update history request\<close>
      sid' \<notin> live s (Client cid) \<comment> \<open>The old server is known to be dead\<close>
    ) else
      op \<notin> uops s \<comment> \<open>We generate a fresh, unique id\<close>
    )"

text\<open>Definition used for @{term m1_P_req}\<close>
text\<open>Conditional append. The result is h appended with op, or just h, if h already contains op.
The if case can occur when a backup that had already received a sync with (cuid, op) suddenly 
becomes the primary (and the previous primary crashed before it could complete the transaction with
the client, i.e., sync with all the backups and send back the response to the client).\<close>
definition cond_app where
  "cond_app h op = (if op \<in> set h then h else h @ [op])"

text\<open>Definition used for @{term m1_P_res}\<close>
text\<open>Is server sid the only one known to be alive? Used for the @{term "m1_P_res"} event below.\<close>
definition singleton_live where
  "singleton_live s sid \<equiv> 
    (\<forall>b . b \<in> live s (Server sid) \<longrightarrow> b = sid)"

lemma singleton_liveI: "\<lbrakk>\<And>b . b \<in> live s (Server sid) \<Longrightarrow> b = sid\<rbrakk> \<Longrightarrow> singleton_live s sid" 
  by(simp add: singleton_live_def)

lemma singleton_liveD: "\<lbrakk>singleton_live s sid; b \<in> live s (Server sid)\<rbrakk> \<Longrightarrow> b = sid" 
  by(simp add: singleton_live_def)

text\<open>The primary server collects the responses from all backup servers. This requires a case 
distinction on whether there exist any backups that have not died yet. If not, then the primary is 
the only alive server and may proceed using his spend history. If there are backups, then they all 
must have sent replies. Used for the @{term m1_P_res} event below.\<close>
definition collect_res where
  "collect_res s sid op h \<equiv> 
    (if singleton_live s sid
     then spend s sid = h
     else (\<forall>sid' \<in> live s (Server sid). sid \<noteq> sid' 
          \<longrightarrow> ss_recv_msg s ssibuf sid' sid (m1_Sync_res op h)))" \<comment> \<open>Note that require at least one 
backup to be alive, such that @{term collect_res} is not trivially satisfied because of a lack of living 
backup servers from which a reply can be expected.\<close> 

lemma collect_resI: 
  "\<lbrakk>\<And>sid'. \<lbrakk>sid' \<in> live s (Server sid); sid \<noteq> sid'\<rbrakk> 
  \<Longrightarrow> ss_recv_msg s ssibuf sid' sid (m1_Sync_res op h);
  singleton_live s sid \<Longrightarrow> spend s sid = h\<rbrakk> \<Longrightarrow> collect_res s sid op h"
  by(auto simp add: collect_res_def)

lemma collect_resD: 
  "\<lbrakk>collect_res s sid op h; sid' \<in> live s (Server sid); sid \<noteq> sid'\<rbrakk> 
  \<Longrightarrow> ss_recv_msg s ssibuf sid' sid (m1_Sync_res op h)"
  "\<lbrakk>collect_res s sid op h; singleton_live s sid\<rbrakk> 
  \<Longrightarrow> spend s sid = h"
  by(auto simp add: collect_res_def dest: singleton_liveD)


(**************************************************************************************************)
(**************************************************************************************************)
subsection \<open>Events\<close>
text\<open>The typical order of events in the absence of failures is as follows:

\begin{itemize}
\item Step 1: @{term m1_C_req}. The client generates a new update request containing a unique operation uop and 
sends it to the current primary server.
\item Step 2: @{term m1_P_req}. The primary receives a request by the client containing a uop. It adds uop to its
pending history and sends sync requests containing both uop and the pending history to all backup
servers.
\item Step 3: @{term m1_B_sync}. Each backup server receives a sync requests, updates its own history with the
history contained in the request, and sends a response.
\item Step 4: @{term m1_P_res}. The primary server, once it receives successfully responses from all backup servers
believed to be alive, updates its own history and sends it back to the client.
\item Step 5: @{term m1_C_res}. The client receives the response by the server and is happy.
\end{itemize}

Failures (@{term m1_Detect_failure}) can happen at any moment and can create a number of situations:
\begin{itemize}
\item  if the primary server fails and a client sends a request to this former primary because it has not
noticed its death, the client will have to resend its request once it does notice it (@{term m1_C_repeat_req}.
\item  if a backup server fails before it has processed the primary's sync request, then the primary will
not be able to proceed until it notices the failure -- since it waits until all live servers have 
responded.
\item  a primary server failing after sending out one or more sync requests is the most complex failure
scenario. Among the remaining servers the one with the lowest server ID will take over, either when
it notices all servers with smaller sids to be dead, or when it receives a client request. In that 
moment, the new primary's history may not have been fully synchronized among all backups (since it 
may have received sync requests by the old primary that other servers have not yet processed). Thus,
the new primary will have to sync its own history with the remaining servers. It does so when 
receiving a client request (which is either a new request or a resend request). The client's uop may
already be contained in the history, in which case it is not added, but synchronization nevertheless
takes place. Note that if a new primary takes over, the order in which pending uops are added to the
history may change (compared to the order in which the old primary appended them to his history). The
order of uops is only fixed once their corresponding syncs are complete.
\item  if all servers fail, the client cannot do anything. We don't execute any event for this case.
\end{itemize}
\<close>

locale loc1 = 
  fixes sidset :: "sid set"
begin

subsubsection \<open>Client events\<close>

text\<open>The bool @{term is_resend} distinguishes two variants of this event: either, the request is new (and
op is a fresh uop. Or the request is a resend to the new primary after the old primary died.\<close>
definition 
  m1_C_req :: "cid \<Rightarrow> sid \<Rightarrow> 'uop => bool \<Rightarrow> 'uop m1_trans" where
  "m1_C_req cid sid op is_resend s s' \<longleftrightarrow> 
     \<comment> \<open>Either generate a new request, or pick an existing request that has to be re-sent, because it
was sent to a primary that is no longer alive\<close>
    cond_request s cid sid op is_resend \<and> 
     \<comment> \<open>The server sid is believed to be the primary, i.e., alive and minimal\<close>
    prim s (Client cid) = Some sid \<and>
    
    s' = s\<lparr>
      \<comment> \<open>send request from client to server\<close>
      csobuf := app_msg s csobuf cid sid (m1_Upd_req op),
      \<comment> \<open>Add a new pending request. If the uid was generated freshly, this entry should be 
          None in the previous state. If we are resending a request, then we simply overwrite the 
          current pending request. We don't bother to delete the old pending request since
          we do not verify liveness guarantees.\<close>
      cpend := fun_upd3 (cpend s) cid sid op True,
      \<comment> \<open>Mark uop as not being fresh anymore.\<close>
      uops := (if is_resend then uops s else insert op (uops s))\<rparr>"

definition 
  m1_C_res :: "cid \<Rightarrow> sid \<Rightarrow> 'uop \<Rightarrow> 'uop history \<Rightarrow> 'uop m1_trans" where
  "m1_C_res cid sid op h s s' \<longleftrightarrow> 
    recv_msg s scibuf sid cid (m1_Upd_res op h) \<and>
    \<comment> \<open>Action\<close>
    s' = s\<lparr>
      \<comment> \<open>Remove the request from the set of pending requests. (This is not strictly necessary: as
          uids are only used once, this state should never be overwritten or read again.)\<close>
      cpend := fun_upd3 (cpend s) cid sid op False,
      \<comment> \<open>Remove message\<close>
      scibuf := rm_msg s scibuf sid cid
\<rparr>"
subsubsection \<open>Primary server events\<close>

text\<open>A server behaves like a primary server as soon as a client treats it like a primary server --
by sending a Client req. Due to perfect failure detection we know that all previous primary servers
must have already failed.\<close>
definition
  m1_P_req :: "sid \<Rightarrow> cid \<Rightarrow> 'uop \<Rightarrow> 'uop history \<Rightarrow> 'uop m1_trans" where
  "m1_P_req sid cid op h s s' \<longleftrightarrow> 
    \<comment> \<open>The primary server must be alive.\<close>
    alive s sid \<and>
    \<comment> \<open>receive an update request from client.\<close>
    recv_msg s csibuf cid sid (m1_Upd_req op) \<and>
    \<comment> \<open>Add op to the history h, unless it already exists there. h is synced with the backup
        servers, but the local state of the primary is only overwritten with h when all alive
        backups have synced.\<close>
    h = cond_app (spend s sid) op \<and>
    \<comment> \<open>initiate syncing with backups, update list of live servers, and store map from suid to cuid.\<close>
    s' = s\<lparr>
      \<comment> \<open>By receiving a client request, this server knows that it is the primary. Thus, it is safe
         to mark all servers with a smaller sid as being dead. (Note: this step is not just safe but necessary
         to prevent the server from later processing sync requests from a dead former primary server.)\<close>
      live := (live s)(Server sid := live_geq s sid sid),
      \<comment> \<open>remove the request from the input channel.\<close>
      csibuf := rm_msg s csibuf cid sid,
      \<comment> \<open>put a message for each live server in the output buffer ('broadcast')\<close>
      ssobuf := (ssobuf s)(sid := 
        (\<lambda> rcv . (if rcv > sid \<and> rcv \<in> live s (Server sid)
                  then (ssobuf s sid rcv) @ [m1_Sync_req op h] else ssobuf s sid rcv))),
      \<comment> \<open>store the map from of the fresh server uid back to the client uid\<close>
      spend := (spend s)(sid := h),
      uopcid := (uopcid s)(sid := (uopcid s sid)(op := Some cid))
    \<rparr>"

text\<open>Server response event\<close>
definition
  m1_P_res :: "sid \<Rightarrow> cid \<Rightarrow> 'uop \<Rightarrow> 'uop history \<Rightarrow> 'uop m1_trans" where
  "m1_P_res sid cid op h s s' \<longleftrightarrow> 
    alive s sid \<and>
    \<comment> \<open>Collect the responses by all backup servers (if there are any) or require h = spend (otherwise).\<close> 
    collect_res s sid op h \<and>  
   
    \<comment> \<open>find matching client uid in the state.\<close> 
    uopcid s sid op = Some cid \<and>

    s' = s\<lparr>
      \<comment> \<open>send response to client.\<close> 
      scobuf := app_msg s scobuf sid cid (m1_Upd_res op h),
      \<comment> \<open>remove messages from input channel.\<close>
      ssibuf := (\<lambda> a b . (if a \<in> live s (Server b) \<and> b = sid \<and> a \<noteq> b then  
          tl (ssibuf s a b) else (ssibuf s a b))),
      \<comment> \<open>update the own history 'hist s sid sid' as well as the 'last received from' history for 
      all live backups sid' (which are guaranteed to be >= sid by @{term inv_sync_prim}). )\<close>
      hist := (hist s)(sid := 
        (\<lambda>sid' . if sid' \<in> live s (Server sid) then h else hist s sid sid'))
    \<rparr>"

subsubsection \<open>Backup server events\<close>
definition
  m1_B_sync :: "sid \<Rightarrow> sid \<Rightarrow> 'uop \<Rightarrow> 'uop history \<Rightarrow> 'uop m1_trans" where
  "m1_B_sync sid pr op h s s' \<longleftrightarrow> 
    alive s sid \<and>
    ss_recv_msg s ssibuf pr sid (m1_Sync_req op h) \<and>
    pr \<in> live s (Server sid) \<and>            \<comment> \<open>primary is still believed to be alive\<close>
    
    s' = s\<lparr> 
      \<comment> \<open>We know that all servers that have a lower server id than the server from which we received
          the request (prim) are dead, due to the assumption of perfect failure detection.
          Removing them is absolutely crucial. Without it, the backup could later falsely accept a sync
          from a server that is no longer the primary (but still believed to be the primary), and
          overwrite the history taken over from the actual primary. This may shorten the history or
          change the order of operations on the history.\<close>
      live := (live s)(Server sid := live_geq s sid pr),
      \<comment> \<open>update last 'received from pr' history and own history\<close>
      hist := (hist s)(sid := ((hist s) sid)(pr := h, sid := h)),
      \<comment> \<open>remove the request from the input channel.\<close>
      ssibuf := ss_rm_msg s ssibuf pr sid,
      \<comment> \<open>send reply back to primary server.\<close>
      ssobuf := ss_app_msg s ssobuf sid pr (m1_Sync_res op h),
      \<comment> \<open>Just in case it becomes primary, it needs to overwrite spend, because spend is the 
          state in which the current history is stored on the primary.\<close>
      spend := (spend s)(sid := h)
    \<rparr>"

text \<open>Remove messages from the head of input buffers non-deterministically. This is needed, for 
instance, to purge sync requests from servers that are known to be dead by the backup.
Since our buffers are FIFOs, not removing messages would block a server.\<close>

definition
  m1_S_purge :: "sid \<Rightarrow> sid \<Rightarrow> 'uop m1_trans" where
  "m1_S_purge a b s s' \<longleftrightarrow>  
    (\<exists> m . ss_recv_msg s ssibuf a b m) \<and>
    s' = s\<lparr> ssibuf := ss_rm_msg s ssibuf a b \<rparr> "

subsubsection \<open>Environment events\<close>
text \<open>Send and receive\<close>
definition m1_cs_Send :: "cid \<Rightarrow> sid \<Rightarrow> 'uop m1_upd \<Rightarrow> 'uop m1_trans" where 
  "m1_cs_Send sa ra m s s' \<longleftrightarrow>
    recv_msg s csobuf sa ra m \<and>
    s' = s\<lparr>csobuf := rm_msg s csobuf sa ra, cschan := app_msg s cschan sa ra m\<rparr>"

definition m1_sc_Send :: "sid \<Rightarrow> cid \<Rightarrow> 'uop m1_upd \<Rightarrow> 'uop m1_trans" where 
  "m1_sc_Send sa ra m s s' \<longleftrightarrow>
    recv_msg s scobuf sa ra m \<and>
    s' = s\<lparr>scobuf := rm_msg s scobuf sa ra, scchan := app_msg s scchan sa ra m\<rparr>"

definition m1_ss_Send :: "sid \<Rightarrow> sid \<Rightarrow> 'uop m1_sync \<Rightarrow> 'uop m1_trans" where 
  "m1_ss_Send sa ra m s s' \<longleftrightarrow>
    ss_recv_msg s ssobuf sa ra m \<and>
    s' = s\<lparr>ssobuf := ss_rm_msg s ssobuf sa ra, sschan := ss_app_msg s sschan sa ra m\<rparr>"

definition m1_cs_Recv :: "cid \<Rightarrow> sid \<Rightarrow> 'uop m1_upd \<Rightarrow> 'uop m1_trans" where 
  "m1_cs_Recv sa ra m s s' \<longleftrightarrow>
    recv_msg s cschan sa ra m \<and>
    s' = s\<lparr>cschan := rm_msg s cschan sa ra, csibuf := app_msg s csibuf sa ra m\<rparr>"

definition m1_sc_Recv :: "sid \<Rightarrow> cid \<Rightarrow> 'uop m1_upd \<Rightarrow> 'uop m1_trans" where 
  "m1_sc_Recv sa ra  m s s' \<longleftrightarrow>
    recv_msg s scchan sa ra m \<and>
    s' = s\<lparr>scchan := rm_msg s scchan sa ra, scibuf := app_msg s scibuf sa ra m\<rparr>"

definition m1_ss_Recv :: "sid \<Rightarrow> sid \<Rightarrow> 'uop m1_sync \<Rightarrow> 'uop m1_trans" where 
  "m1_ss_Recv sa ra m s s' \<longleftrightarrow>
    ss_recv_msg s sschan sa ra m \<and>
    s' = s\<lparr>sschan := ss_rm_msg s sschan sa ra, ssibuf := 
      (if sa \<in> live s (Server ra) then ss_app_msg s ssibuf sa ra m else ssibuf s)\<rparr>"

text \<open>Remove an element x from a set H. If x is not contained in H, returns H.\<close>
definition remove :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "remove x H = H - {x}"

text \<open>Failure detector for either Client or Server.
      This event removes a single server from the list of servers believed to be alive which is kept
      in the local state of some agent. When a server dies, it first is removed from the its own
      live set to represent failures. Subsequently, this failure can be detected by other agents, too.
      Invariant @{term inv_alive} shows that a server knowing itself to be alive implies that everyone 
      believes it is live.\<close>
definition
  m1_Detect_failure :: "agent \<Rightarrow> sid \<Rightarrow> 'uop m1_trans" where  
  "m1_Detect_failure agt sid s s' \<longleftrightarrow> 
    (if sid \<in> elive s 
    then agt = Server sid \<and> s' = s\<lparr> live := (live s)(agt := remove sid (live s agt)), elive := remove sid (elive s) \<rparr>
    else s' = s\<lparr> live := (live s)(agt := remove sid (live s agt)) \<rparr>
)"

end

(**************************************************************************************************)
(**************************************************************************************************)
subsection \<open>Transition system.\<close>

datatype 'uop m1_event = 
  B1_C_req cid sid "'uop" bool |
  B1_C_res cid sid "'uop" "'uop history" |
  B1_P_req sid cid "'uop" "'uop history" |
  B1_P_res sid cid "'uop" "'uop history" |
  B1_B_sync sid sid 'uop "'uop history" |
  B1_S_purge sid sid |
  B1_cs_Send cid sid "'uop m1_upd" |
  B1_sc_Send sid cid "'uop m1_upd" |
  B1_ss_Send sid sid "'uop m1_sync" |
  B1_cs_Recv cid sid "'uop m1_upd" |
  B1_sc_Recv sid cid "'uop m1_upd" |
  B1_ss_Recv sid sid "'uop m1_sync" |
  B1_Detect_failure agent sid |
  B1_Skip

context loc1 begin
fun m1_trans :: "'uop m1_state \<Rightarrow> 'uop m1_event \<Rightarrow> 'uop m1_state \<Rightarrow> bool"  where
  "m1_trans s (B1_C_req cid sid op is_resend) s' \<longleftrightarrow> m1_C_req cid sid op is_resend s s'" | 
  "m1_trans s (B1_C_res cid sid op h) s' \<longleftrightarrow> m1_C_res cid sid op h s s'" | 
  "m1_trans s (B1_P_req sid cid op h') s' \<longleftrightarrow> m1_P_req sid cid op  h' s s'" | 
  "m1_trans s (B1_P_res sid cid op h) s' \<longleftrightarrow> m1_P_res sid cid op h s s'" | 
  "m1_trans s (B1_B_sync sid pr op h) s' \<longleftrightarrow> m1_B_sync sid pr op h s s'" | 
  "m1_trans s (B1_S_purge a b) s' \<longleftrightarrow> m1_S_purge a b s s'" | 
  "m1_trans s (B1_cs_Send sa ra m) s' \<longleftrightarrow> m1_cs_Send sa ra m s s'" | 
  "m1_trans s (B1_sc_Send sa ra m) s' \<longleftrightarrow> m1_sc_Send sa ra m s s'" | 
  "m1_trans s (B1_ss_Send sa ra m) s' \<longleftrightarrow> m1_ss_Send sa ra m s s'" | 
  "m1_trans s (B1_cs_Recv sa ra m) s' \<longleftrightarrow> m1_cs_Recv sa ra m s s'" | 
  "m1_trans s (B1_sc_Recv sa ra m) s' \<longleftrightarrow> m1_sc_Recv sa ra m s s'" | 
  "m1_trans s (B1_ss_Recv sa ra m) s' \<longleftrightarrow> m1_ss_Recv sa ra m s s'" | 
  "m1_trans s (B1_Detect_failure agt sid) s' \<longleftrightarrow> m1_Detect_failure agt sid s s'" | 
  "m1_trans s B1_Skip s' \<longleftrightarrow> s = s'"

lemmas m1_trans_cases [elim!] = m1_trans.elims(2)    \<comment> \<open>always decompose\<close> (*copied this from Leader Election*)

definition 
  m1 :: "('uop m1_event, 'uop m1_state) ES" where
  "m1 \<equiv> \<lparr>
    init = (\<lambda>s . m1_init sidset s),
    trans = m1_trans
  \<rparr>"

lemmas m1_trans_defs = m1_C_req_def  m1_C_res_def m1_P_req_def m1_P_res_def m1_B_sync_def 
  m1_S_purge_def m1_cs_Send_def m1_sc_Send_def m1_ss_Send_def m1_cs_Recv_def m1_sc_Recv_def 
  m1_ss_Recv_def m1_Detect_failure_def
lemmas m1_defs = m1_def m1_init_def m1_trans_defs


(**************************************************************************************************)
subsubsection \<open>Helpful definitions and lemmas of the system\<close>

text\<open>The following definitions specify that sync messages exist in the network. They are used only
in defining the invariants, not in the specification of the event system.\<close>
definition sync_req_ex where 
  "sync_req_ex s p b m \<equiv> \<exists> op h . m = m1_Sync_req op h \<and> (m \<in> set (ssobuf s p b) 
      \<or> m \<in> set (sschan s p b) \<or> m \<in> set (ssibuf s p b))"

definition sync_res_ex where 
  "sync_res_ex s p b m \<equiv> \<exists> op h . m = m1_Sync_res op h \<and> (m \<in> set (ssobuf s b p) 
      \<or> m \<in> set (sschan s b p) \<or> m \<in> set (ssibuf s b p))"

definition sync_ex where
  "sync_ex s p b m \<equiv> (sync_req_ex s p b m \<or> sync_res_ex s p b m)"

definition upd_req_ex where 
  "upd_req_ex s c p m \<equiv> m \<in> set (csobuf s c p) \<or> m \<in> set (cschan s c p) 
                                 \<or> m \<in> set (csibuf s c p)"

definition upd_res_ex where 
  "upd_res_ex s c p m \<equiv> m \<in> set (scobuf s c p) \<or> m \<in> set (scchan s c p) 
                                 \<or> m \<in> set (scibuf s c p)"

lemmas sync_ex_defs = sync_ex_def sync_res_ex_def sync_req_ex_def

lemma collect_res_sync_res_ex: 
  "\<lbrakk>collect_res s sid op h; sid' \<in> live s (Server sid); sid \<noteq> sid'\<rbrakk> 
  \<Longrightarrow> sync_res_ex s sid sid' (m1_Sync_res op h)"
  by(auto simp add: sync_res_ex_def dest!: collect_resD(1))

lemma sync_set_exI: 
  "\<lbrakk>m \<in> set (ssobuf s p b); m = m1_Sync_req op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  "\<lbrakk>m \<in> set (sschan s p b); m = m1_Sync_req op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  "\<lbrakk>m \<in> set (ssibuf s p b); m = m1_Sync_req op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  "\<lbrakk>m \<in> set (ssobuf s b p); m = m1_Sync_res op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  "\<lbrakk>m \<in> set (sschan s b p); m = m1_Sync_res op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  "\<lbrakk>m \<in> set (ssibuf s b p); m = m1_Sync_res op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  by(auto simp add: sync_ex_defs)

lemma sync_res_set_exI: 
  "\<lbrakk>m \<in> set (ssobuf s b p); m = m1_Sync_res op h\<rbrakk> \<Longrightarrow> sync_res_ex s p b m"
  "\<lbrakk>m \<in> set (sschan s b p); m = m1_Sync_res op h\<rbrakk> \<Longrightarrow> sync_res_ex s p b m"
  "\<lbrakk>m \<in> set (ssibuf s b p); m = m1_Sync_res op h\<rbrakk> \<Longrightarrow> sync_res_ex s p b m"
  by(auto simp add: sync_res_ex_def)

lemma sync_exI: 
  "\<lbrakk>ssobuf s p b = m # xs; m = m1_Sync_req op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  "\<lbrakk>sschan s p b = m # xs; m = m1_Sync_req op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  "\<lbrakk>ssibuf s p b = m # xs; m = m1_Sync_req op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  "\<lbrakk>ssobuf s b p = m # xs; m = m1_Sync_res op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  "\<lbrakk>sschan s b p = m # xs; m = m1_Sync_res op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  "\<lbrakk>ssibuf s b p = m # xs; m = m1_Sync_res op h\<rbrakk> \<Longrightarrow> sync_ex s p b m"
  by(auto simp add: sync_ex_defs)

lemma upd_req_ex_Server:
  "m1_P_req sid cid op h' s s' \<Longrightarrow> upd_req_ex s cid sid (m1_Upd_req op)"
  by(auto simp add: m1_defs upd_req_ex_def)

lemma sync_ex_Backup: "m1_B_sync sid pr op h s s' \<Longrightarrow> sync_ex s pr sid (m1_Sync_req op h)"
  by(auto simp add: m1_defs sync_ex_defs)

lemma sync_req_ex_Backup: 
  "m1_B_sync sid pr op h s s' \<Longrightarrow> sync_req_ex s pr sid (m1_Sync_req op h)"
  by(auto simp add: m1_defs sync_ex_defs)

lemma sync_res_ex_Backup: "m1_B_sync sid pr op h s s' \<Longrightarrow> sync_res_ex s' pr sid (m1_Sync_res op h)"
  by(auto simp add: m1_defs sync_ex_defs)

lemma sync_ex_Server_res: 
  "\<lbrakk>m1_P_res sid cid op h s s'; \<not>singleton_live s sid\<rbrakk> \<Longrightarrow> \<exists>b . sync_ex s sid b (m1_Sync_res op h)"
  apply(auto simp add: m1_defs sync_ex_defs singleton_live_def)
  by (metis (no_types, lifting) collect_res_sync_res_ex sync_res_ex_def)



(**************************************************************************************************)
(**************************************************************************************************)
subsection \<open>Characterization of events\<close>

text \<open>No zombie servers that become live after being declared dead.\<close>
lemma live_mono: 
  "\<lbrakk>m1_C_req cid sid op is_resend s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_C_res cid sid op h s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_P_req sid cid op h' s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_P_res sid cid op h s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_B_sync sid pr op h s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_S_purge sid sid' s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_cs_Send csa ra mc s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_sc_Send sa cra mc s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_ss_Send sa ra m s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_cs_Recv csa ra mc s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_sc_Recv sa cra mc s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_ss_Recv sa ra m s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  "\<lbrakk>m1_Detect_failure agt sid s s'; x \<in> live s' ag\<rbrakk> \<Longrightarrow> x \<in> live s ag" 
  by(auto simp add: m1_defs remove_def live_geq_def)

lemma alive_mono: "\<lbrakk>m1_trans s e s'; alive s' x\<rbrakk> \<Longrightarrow> alive s x" (*needed?*)
  by(auto simp add: m1_defs remove_def)

lemma m1_P_req_live_geq:
  "\<lbrakk>m1_P_req sid cid op h' s s'; x \<in> live s' (Server sid)\<rbrakk> \<Longrightarrow> x \<ge> sid"
  by(auto simp add: m1_defs live_geq_def)

text\<open>@{term sync_ex} is almost monotonic; the only exception is @{term m1_P_req}\<close>
lemma sync_ex_almost_mono:
  "\<lbrakk>m1_C_req cid sid op is_resend s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_C_res cid sid op h s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_P_res sid cid op h s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_B_sync sid pr op h s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> \<exists>m' . sync_ex s p b m'" 
  "\<lbrakk>m1_S_purge sid sid' s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_cs_Send csa ra mc s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_sc_Send sa cra mc s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_ss_Send sa ra ms s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_cs_Recv csa ra mc s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_sc_Recv sa cra mc s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_ss_Recv sa ra ms s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_Detect_failure agt sid s s'; sync_ex s' p b m\<rbrakk> \<Longrightarrow> sync_ex s p b m" 
  "\<lbrakk>m1_P_req sid cid op h' s s'; sync_ex s' p b m; m \<noteq> m1_Sync_req op h' \<or> sid \<noteq> p\<rbrakk> 
    \<Longrightarrow> sync_ex s p b m" 
  apply(auto simp add: m1_defs)
  subgoal by (auto simp add: sync_ex_defs tl_Nil intro: list.set_sel(2))
  subgoal by (auto simp add: sync_ex_defs tl_Nil intro: list.set_sel(2))
  subgoal by (auto simp add: sync_ex_defs tl_Nil intro: list.set_sel(2))
  subgoal by (auto simp add: sync_ex_defs tl_Nil intro: list.set_sel(2)) (*takes a few sec*)
  subgoal 
    apply (cases "m = m1_Sync_res op h \<and> pr = p \<and> sid = b")
    subgoal
      apply(rule exI[of _ "m1_Sync_req op h"])
      by(auto simp add: sync_ex_defs)
    subgoal
      by(auto intro!: exI[of _ m] simp add: sync_ex_defs) (*takes a few sec*)
    done
  by (auto simp add: sync_ex_defs tl_Nil intro: list.set_sel(2)) (*takes a few sec*)

    
text\<open>@{term sync_req_ex} is almost monotonic; the only exception is @{term m1_P_req}\<close>
lemma sync_req_ex_almost_mono:
  "\<lbrakk>m1_C_req cid sid op is_resend s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_C_res cid sid op h s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_P_res sid cid op h s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_B_sync sid pr op h s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_S_purge sid sid' s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_cs_Send csa ra mc s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_sc_Send sa cra mc s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_ss_Send sa ra ms s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_cs_Recv csa ra mc s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_sc_Recv sa cra mc s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_ss_Recv sa ra ms s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  "\<lbrakk>m1_Detect_failure agt sid s s'; sync_req_ex s' p b m\<rbrakk> \<Longrightarrow> sync_req_ex s p b m" 
  by(auto simp add: m1_defs)
    (auto simp add: sync_ex_defs tl_Nil intro: list.set_sel(2)) (*takes a few sec*)
  

text\<open>@{term sync_res_ex} is almost monotonic; the only exception is @{term m1_B_sync}\<close>
lemma sync_res_ex_almost_mono:
  "\<lbrakk>m1_C_req cid sid op is_resend s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_C_res cid sid op h s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_P_req sid cid op h' s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_P_res sid cid op h s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_S_purge sid sid' s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_cs_Send csa ra mc s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_sc_Send sa cra mc s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_ss_Send sa ra ms s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_cs_Recv csa ra mc s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_sc_Recv sa cra mc s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_ss_Recv sa ra ms s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  "\<lbrakk>m1_Detect_failure agt sid s s'; sync_res_ex s' p b m\<rbrakk> \<Longrightarrow> sync_res_ex s p b m" 
  by(auto simp add: m1_defs)
    (auto simp add: sync_res_ex_def tl_Nil intro: list.set_sel(2)) (*takes a few sec*)
  


text\<open>@{term upd_req_ex} is almost monotonic; the only exception are @{term m1_C_req} and @{term m1_C_repeat_req}.\<close>
lemma upd_req_ex_almost_mono:
  "\<lbrakk>m1_C_res cid sid op h s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_P_req sid cid op h' s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_P_res sid cid op h s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_B_sync sid pr op h s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_S_purge sid sid' s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_cs_Send csa ra mc s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_sc_Send sa cra mc s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_ss_Send sa ra ms s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_cs_Recv csa ra mc s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_sc_Recv sa cra mc s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_ss_Recv sa ra ms s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  "\<lbrakk>m1_Detect_failure agt sid s s'; upd_req_ex s' p b m\<rbrakk> \<Longrightarrow> upd_req_ex s p b m" 
  by(auto simp add: m1_defs)
    (auto simp add: upd_req_ex_def tl_Nil intro: list.set_sel(2)) (*takes a few sec*)


(**************************************************************************************************)
(**************************************************************************************************)
subsection \<open>Invariants\<close>
subsubsection \<open>@{term inv_upd_req}\<close>
text \<open>This states that if an update requests from client c to primary p exists, then c knows all
servers smaller than p to be definitely dead. This implies that they are not alive from a global
point of view, which means they can safely be removed from p's liveset as well (safely meaning that
removing them from the p's liveset does not cause a server to die -- all removed servers were 
already dead).\<close>
definition inv_upd_req where
  "inv_upd_req s \<equiv> 
(\<forall> c p m . upd_req_ex s c p m \<longrightarrow> (\<forall> sid'. sid' \<in> live s (Client c) \<longrightarrow> sid' \<ge> p))"

lemma inv_upd_reqD: 
  "\<lbrakk>inv_upd_req s; upd_req_ex s c p m; sid' \<in> live s (Client c)\<rbrakk> \<Longrightarrow> sid' \<ge> p"
  by(auto simp add: inv_upd_req_def)

lemma inv_upd_reqE: 
"\<lbrakk>inv_upd_req s; 
\<lbrakk>\<And> c p sid' m . \<lbrakk>upd_req_ex s c p m; sid' \<in> live s (Client c)\<rbrakk> \<Longrightarrow> sid' \<ge> p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: inv_upd_req_def)

lemma inv_upd_reqI: 
"\<lbrakk>\<And> c p m sid' . \<lbrakk>upd_req_ex s c p m; sid' \<in> live s (Client c)\<rbrakk> \<Longrightarrow> sid' \<ge> p\<rbrakk> 
\<Longrightarrow> inv_upd_req s"
  by(auto simp add: inv_upd_req_def)

lemma upd_req_ex_mono_inv: 
  "\<lbrakk>inv_upd_req s; \<And> c p m. upd_req_ex s' c p m \<Longrightarrow> upd_req_ex s c p m; 
  \<And> a b . a \<in> live s' (Client b) \<Longrightarrow> a \<in> live s (Client b)\<rbrakk>\<Longrightarrow> inv_upd_req s'"
  by(auto intro!: inv_upd_reqI dest!: inv_upd_reqD)

lemma Inv_inv_upd_req: 
  "Inv m1 inv_upd_req"
proof(rule Invariant_rule)
  fix s::"'uop m1_state" 
  fix e s'
  assume asm: "m1: s\<midarrow>e\<rightarrow> s'" "reach m1 s" "inv_upd_req s"
  then show "inv_upd_req s'" using \<open>m1: s\<midarrow>e\<rightarrow> s'\<close> 
  proof (auto simp add: m1_def)
    fix sid cid op is_resend
    assume assm: "inv_upd_req s" "m1_C_req cid sid op is_resend s s'" 
    show "inv_upd_req s'" 
      apply(rule inv_upd_reqI)
      subgoal for x y m sid'
        apply(cases "sid = y")
        using assm apply(auto dest!: inv_upd_reqD simp add: m1_defs upd_req_ex_def)
        using primD(3) by auto
      done
  qed(auto elim!: upd_req_ex_mono_inv upd_req_ex_almost_mono live_mono)  
qed (auto simp add: inv_upd_req_def m1_defs upd_req_ex_def)



(**************************************************************************************************)
(**************************************************************************************************)
subsubsection \<open>@{term inv_sync_prim}\<close>

text\<open>@{term inv_sync_prim}: If a sync message (sync request from p to b or sync reply from b to p) is in 
the system (obuf, chan, ibuf), then p *knows* that all servers smaller than p are dead.
Due to perfect failure detection this implies that they are actually dead. Note that this holds
independently of whether p is alive or not. Intuitively this holds, since p will only send out a sync
if he determined to be the primary, which requires all smaller servers to be (known to be) dead.

(Previously we had a weaker invariant that only stated that the servers smaller than p are dead, but
not that p knows that they are dead. This proved to be insufficient for proving the 
@{term backup_consistency} lemma below.)

We phrase this invariant as the contraposition:\<close>
definition inv_sync_prim where
  "inv_sync_prim s \<equiv> 
  (\<forall> p b m . sync_ex s p b m \<longrightarrow> (\<forall> sid'. sid' \<in> live s (Server p) \<longrightarrow> sid' \<ge> p) \<and> p < b)"

lemma inv_sync_primD: 
"\<lbrakk>inv_sync_prim s; sync_ex s p b m; sid' \<in> live s (Server p)\<rbrakk> \<Longrightarrow> sid' \<ge> p"
"\<lbrakk>inv_sync_prim s; sync_ex s p b m\<rbrakk> \<Longrightarrow> p < b"
  by(auto simp add: inv_sync_prim_def)

lemma inv_sync_primI: 
  "\<lbrakk>\<And> p b m sid' . \<lbrakk>sync_ex s p b m; sid' \<in> live s (Server p)\<rbrakk> \<Longrightarrow> sid' \<ge> p;
\<And> p b m sid' . \<lbrakk>sync_ex s p b m\<rbrakk> \<Longrightarrow> p < b\<rbrakk> \<Longrightarrow> inv_sync_prim s"
  by(auto simp add: inv_sync_prim_def)

text\<open>Observation: removing servers from the liveset can never make @{term inv_sync_prim} not true:\<close>
lemma sync_ex_mono_inv_sync_prim: 
  "\<lbrakk>inv_sync_prim s; \<And> p b m. sync_ex s' p b m \<Longrightarrow> sync_ex s p b m; 
  \<And> a b . a \<in> live s' (Server b) \<Longrightarrow> a \<in> live s (Server b)\<rbrakk>\<Longrightarrow> inv_sync_prim s'"
  by(fastforce intro!: inv_sync_primI dest: inv_sync_primD)

lemma inv_sync_prim_trans:
  assumes "m1: s\<midarrow>e\<rightarrow> s'" "inv_sync_prim s"
  shows "inv_sync_prim s'"
  using assms apply - 
  proof (auto simp add: m1_def)
    fix sid cid op h h'
    assume assm: "inv_sync_prim s" "m1_P_req sid cid op h' s s'" 
    show "inv_sync_prim s'" 
      apply(rule inv_sync_primI)
      subgoal for x y m sid'                                                              
        using assm by(auto dest: inv_sync_primD simp add: m1_defs sync_ex_defs live_geq_def dest: sync_set_exI) 
      subgoal for x y m sid'
        apply(cases "sid = x \<and> m = (m1_Sync_req op h')")
        subgoal
          using assm(2) apply(auto simp add: m1_defs sync_ex_defs)
          using assm(1)  by(auto dest: inv_sync_primD intro: sync_set_exI)
        using assm apply(auto simp add: m1_defs) 
        using assm(2) apply-
        by(auto elim!: sync_ex_almost_mono inv_sync_primD(2))
      done
  next
    fix sid pr op h
    assume assm: "inv_sync_prim s" "m1_B_sync sid pr op h s s'" 
    show "inv_sync_prim s'" 
      apply(rule inv_sync_primI)
      subgoal for x y m sid'
        using assm(2) apply(auto dest!: sync_ex_almost_mono)
        using assm by(auto elim!: inv_sync_primD(1) intro: live_mono)
      subgoal for x y m sid'
        apply(cases "sid = y \<and> m = (m1_Sync_res op h)")
        subgoal
          using assm(2) apply(auto simp add: m1_defs sync_ex_defs)
          using assm(1) apply(auto dest: inv_sync_primD intro: sync_set_exI)
          using assm(2) loc1.inv_sync_prim_def loc1.sync_ex_Backup by fastforce
        using assm using inv_sync_primD(2) apply(auto simp add: m1_defs)
        using assm(1) assm(2) inv_sync_primD(2) sync_ex_almost_mono(4) by fast+
      done
  qed(auto elim!: sync_ex_mono_inv_sync_prim sync_ex_almost_mono live_mono) 

lemma Inv_inv_sync_prim: 
  "Inv m1 inv_sync_prim"
  apply(rule Invariant_rule)
  subgoal by(auto simp add: inv_sync_prim_def m1_defs sync_ex_defs)
  by(elim inv_sync_prim_trans)

lemma inv_sync_prim_trace: "\<lbrakk>m1: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'; inv_sync_prim s\<rbrakk> \<Longrightarrow> inv_sync_prim s'"
  by(induction rule: trace.induct)
    (auto elim: inv_sync_prim_trans)

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection \<open>@{term inv_sync_backup}\<close>

text\<open>This invariant is very similar to @{term inv_sync_prim}, but it only talks about sync reply messages 
(not all sync messages) and it talks about the backup's liveset, rather than the primary's liveset.\<close>
definition inv_sync_backup where
  "inv_sync_backup s \<equiv> (\<forall> p b m . sync_res_ex s p b m \<longrightarrow> 
                          (\<forall> sid'. sid' \<in> live s (Server b) \<longrightarrow> sid' \<ge> p))"

lemma inv_sync_backupD: 
  "\<lbrakk>inv_sync_backup s; sync_res_ex s p b m; sid' \<in> live s (Server b)\<rbrakk> \<Longrightarrow> sid' \<ge> p"
  by(auto simp add: inv_sync_backup_def)

lemma inv_sync_backupI: 
  "\<lbrakk>\<And> p b m sid' . \<lbrakk>sync_res_ex s p b m; sid' \<in> live s (Server b)\<rbrakk> \<Longrightarrow> sid' \<ge> p\<rbrakk> 
  \<Longrightarrow> inv_sync_backup s"
  by(auto simp add: inv_sync_backup_def)

text\<open>Observation: removing servers from the liveset can never make @{term inv_sync_backup} not true:\<close>
lemma sync_res_ex_mono_inv_sync_backup: 
  "\<lbrakk>inv_sync_backup s; \<And> p b m. sync_res_ex s' p b m \<Longrightarrow> sync_res_ex s p b m; 
  \<And> a b . a \<in> live s' (Server b) \<Longrightarrow> a \<in> live s (Server b)\<rbrakk>\<Longrightarrow> inv_sync_backup s'"
  by(auto intro!: inv_sync_backupI dest!: inv_sync_backupD)

lemma m1_B_sync_live: "\<lbrakk>m1_B_sync sid pr op h s s'; sid' \<in> live s' (Server sid)\<rbrakk> \<Longrightarrow> sid' \<ge> pr"
  by(auto simp add: m1_defs live_geq_def)

lemma sync_res_ex_Backup': 
  "\<lbrakk>sync_res_ex s' p b m; m1_B_sync sid pr op h s s'\<rbrakk> 
  \<Longrightarrow> p=pr \<and> b=sid \<and> m=m1_Sync_res op h \<or> sync_res_ex s p b m"
  by(auto simp add: m1_defs sync_ex_defs)

lemma Inv_inv_sync_backup: 
  "Inv m1 inv_sync_backup"
proof(rule Invariant_rule)
  fix s e s'
  assume asm: "m1: s\<midarrow>e\<rightarrow> s'" "reach m1 s" "inv_sync_backup s"
  then show "inv_sync_backup s'" using \<open>m1: s\<midarrow>e\<rightarrow> s'\<close> 
  proof (auto simp add: m1_def)
    fix sid pr op h
    assume assm: "inv_sync_backup s" "m1_B_sync sid pr op h s s'" 
    show "inv_sync_backup s'" 
      apply(rule inv_sync_backupI)
      subgoal for x y m sid'
        apply(cases "sid = x \<or> sid = y")
        subgoal
          using assm apply(auto simp add: m1_defs live_geq_def)
          subgoal
            apply(frule sync_res_ex_Backup') using assm apply (auto dest!: inv_sync_backupD)
            using assm(1) inv_sync_backupD by blast
          apply(frule sync_res_ex_Backup') using assm by (auto dest!: inv_sync_backupD)
        apply(frule sync_res_ex_Backup') using assm by (auto dest!: inv_sync_backupD intro: live_mono)
      done
  qed(auto elim!: sync_res_ex_mono_inv_sync_backup sync_res_ex_almost_mono live_mono)  
qed(auto simp add: inv_sync_backup_def m1_defs sync_res_ex_def)


(**************************************************************************************************)
(**************************************************************************************************)
subsubsection \<open>@{term inv_elive}\<close>

text\<open>@{term inv_elive}: A server knows itself to be alive iff it is globally known to be alive (elive).\<close>
definition inv_elive where
  "inv_elive s \<equiv> (\<forall> sid . sid \<in> elive s \<longleftrightarrow> alive s sid)"

lemma inv_eliveD: "\<lbrakk>inv_elive s\<rbrakk> \<Longrightarrow> sid \<in> elive s \<longleftrightarrow> alive s sid" by(auto simp add: inv_elive_def)

lemma inv_eliveI: 
  "\<lbrakk>\<And> sid . sid \<in> elive s \<longleftrightarrow> alive s sid\<rbrakk> \<Longrightarrow> inv_elive s" by(auto simp add: inv_elive_def)

lemma Inv_inv_elive: 
  "Inv m1 inv_elive"
proof(rule Invariant_rule_Inv[where J="(\<lambda> s. inv_upd_req s \<and> inv_sync_backup s \<and> inv_sync_prim s)"],
      auto intro!: multiple_Inv)
  fix s e s'
  assume asm: "m1: s\<midarrow>e\<rightarrow> s'" "reach m1 s" "inv_elive s" "inv_upd_req s" "inv_sync_prim s"
  then show "inv_elive s'" using \<open>m1: s\<midarrow>e\<rightarrow> s'\<close> 
  proof (auto simp add: m1_def)
    fix sid pr op h
    assume assm: "inv_elive s" "m1_B_sync sid pr op h s s'" 
    show "inv_elive s'" 
    proof (rule inv_eliveI)
      fix x
      have "sync_ex s pr sid (m1_Sync_req op h)"  using assm by(auto simp add: m1_defs intro: sync_exI)
      then show "x \<in> elive s' \<longleftrightarrow> alive s' x"
        using assm asm(5) by(auto simp add: m1_defs live_geq_def dest: inv_eliveD inv_sync_primD(2))
    qed
  qed(auto dest: inv_eliveD intro!: inv_eliveI simp add: m1_defs remove_def live_geq_def) (*takes > 10 sec*)
qed(auto simp add: Inv_inv_upd_req Inv_inv_sync_backup Inv_inv_sync_prim, 
    auto simp add: m1_defs intro: inv_eliveI)

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection \<open>@{term inv_alive}\<close>

text\<open>@{term inv_alive}: If a server knows it is alive, then everyone else also knows that.\<close>
definition inv_alive where
  "inv_alive s \<equiv> (\<forall> sid sid' . alive s sid \<longrightarrow> sid \<in> live s sid')"

lemma inv_aliveD: "\<lbrakk>inv_alive s; alive s sid\<rbrakk> \<Longrightarrow> sid \<in> live s sid'"
  by(auto simp add: inv_alive_def)

lemma inv_aliveI: 
  "\<lbrakk>\<And> sid sid' . \<lbrakk>alive s sid\<rbrakk> \<Longrightarrow> sid \<in> live s sid'\<rbrakk> \<Longrightarrow> inv_alive s"
  by(auto simp add: inv_alive_def)

lemma inv_alive_mono: 
  "\<lbrakk>inv_alive s; alive s x; x \<in> live s y \<Longrightarrow> x \<in> live s' y \<rbrakk> \<Longrightarrow> x \<in> live s' y"
  apply(drule inv_aliveD[of s x y])
  by auto

lemma inv_alive_const: 
  "\<lbrakk>inv_alive s; \<And> x y . x \<in> live s y \<Longrightarrow> x \<in> live s' y; \<And> x y . x \<in> live s' y \<Longrightarrow> x \<in> live s y\<rbrakk> 
\<Longrightarrow> inv_alive s'"
  by(auto intro!: inv_aliveI dest!: inv_aliveD)

lemma inv_alive_contradict: 
  "\<lbrakk>inv_alive s; alive s' x; alive s' x \<Longrightarrow> alive s x; x \<notin> live s ag \<rbrakk> \<Longrightarrow> False"
  apply(drule inv_aliveD[of s x ag])
  by auto

lemma Inv_inv_alive: 
  "Inv m1 inv_alive"
proof(rule Invariant_rule_Inv
      [where J="(\<lambda> s. inv_upd_req s \<and> inv_sync_backup s \<and> inv_sync_prim s \<and> inv_elive s)"],
      auto intro!: multiple_Inv)
  fix s e s'
  assume asm: "m1: s\<midarrow>e\<rightarrow> s'" "reach m1 s" "inv_alive s" "inv_upd_req s" "inv_sync_prim s" "inv_elive s"
  then show "inv_alive s'" using \<open>m1: s\<midarrow>e\<rightarrow> s'\<close> 
  proof (auto simp add: m1_def)
    fix sid cid op h h'
    assume assm: "inv_alive s" "m1_P_req sid cid op h' s s'" 
    show "inv_alive s'" 
    proof (rule inv_aliveI)
      fix x ag
      assume "alive s' x"
      then show "x \<in> live s' ag"
        apply(cases "ag = Server sid \<and> x < sid")
        using assm asm(4)
        by (auto dest!: inv_alive_contradict 
                 dest: upd_req_ex_Server inv_upd_reqD live_mono)
           (auto elim: inv_alive_mono simp add: m1_defs live_geq_def)
    qed
  next
    fix sid pr op h
    assume assm: "inv_alive s" "m1_B_sync sid pr op h s s'" 
    show "inv_alive s'" 
    proof (rule inv_aliveI)
      fix x ag
      assume "alive s' x"
      then show "x \<in> live s' ag"
        apply(cases "ag = Server sid \<and> x < pr")
        using assm asm(5)
        by (auto dest!: inv_alive_contradict 
                 dest: sync_ex_Backup inv_sync_primD live_mono)
           (auto elim: inv_alive_mono simp add: m1_defs live_geq_def)
    qed
  next
    fix agt sid
    assume assm: "inv_alive s" "m1_Detect_failure agt sid s s'" 
    show "inv_alive s'" 
    proof (rule inv_aliveI)
      fix x ag
      assume "alive s' x"
      then show "x \<in> live s' ag"
        apply(cases "alive s sid")
        using assm \<open>inv_elive s\<close>
        by(auto simp add: m1_defs remove_def dest: inv_aliveD inv_eliveD)
    qed
  qed(auto elim!: inv_alive_const dest: live_mono, auto simp add: m1_defs)  
qed(auto simp add: Inv_inv_upd_req Inv_inv_sync_backup Inv_inv_sync_prim Inv_inv_elive, 
    auto simp add: m1_defs intro: inv_aliveI)

lemma inv_alive_partialD: (*needed?!*)
  "\<lbrakk>inv_alive s; alive s sid\<rbrakk> \<Longrightarrow> sid \<in> live s sid'"
  by (auto simp add: inv_alive_def)

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection \<open>@{term inv_uop_history}\<close>
definition inv_uop_history where
  "inv_uop_history s \<equiv> (\<forall> p b op h . sync_req_ex s p b (m1_Sync_req op h) \<or>
                                      sync_res_ex s p b (m1_Sync_res op h) \<longrightarrow> op \<in> set h)"

lemma inv_uop_historyI:
  "\<lbrakk>\<And> p b op h . sync_req_ex s p b (m1_Sync_req op h) \<Longrightarrow> op \<in> set h;
    \<And> p b op h . sync_res_ex s p b (m1_Sync_res op h) \<Longrightarrow> op \<in> set h\<rbrakk>\<Longrightarrow> inv_uop_history s"
  by(auto simp add: inv_uop_history_def)

lemma inv_uop_historyD:
  "\<lbrakk>inv_uop_history s; sync_req_ex s p b (m1_Sync_req op h)\<rbrakk> \<Longrightarrow> op \<in> set h"
  "\<lbrakk>inv_uop_history s; sync_res_ex s p b (m1_Sync_res op h)\<rbrakk> \<Longrightarrow> op \<in> set h"
  by(auto simp add: inv_uop_history_def)

lemma Inv_inv_uop_history: 
  "Inv m1 inv_uop_history"
proof(rule Invariant_rule)
  fix s0::"'uop m1_state"
  assume "init m1 s0"
  then show "inv_uop_history s0" 
    by(auto simp add: inv_uop_history_def m1_defs sync_ex_defs)
next
  fix s::"'uop m1_state" 
  fix e s'
  assume asm: "m1: s\<midarrow>e\<rightarrow> s'" "reach m1 s" "inv_uop_history s"
  then show "inv_uop_history s'" using \<open>m1: s\<midarrow>e\<rightarrow> s'\<close> 
  proof (auto simp add: m1_def)
    fix op::"'uop" 
    fix sid cid op h h'
    assume assum: "inv_uop_history s" "m1_P_req sid cid op h' s s'"
    show "inv_uop_history s'"
    proof(rule inv_uop_historyI)
      fix p b n_op n_h
      assume "sync_req_ex s' p b (m1_Sync_req n_op n_h)"
      then show "n_op \<in> set n_h"
        apply(cases "n_op = op \<and> n_h = h'")
        subgoal apply auto using assum(2) apply(auto simp add: m1_defs)
          by (metis (no_types, lifting) cond_app_def in_set_conv_decomp)
        apply auto using assum(2) apply(auto simp add: m1_defs)
        using assum(1) apply- apply(erule inv_uop_historyD) apply (auto simp add: sync_ex_defs)
        using inv_uop_historyD by (metis sync_req_ex_def)+
    next
      fix p b n_op n_h
      assume "sync_res_ex s' p b (m1_Sync_res n_op n_h)"
      then have "sync_res_ex s p b (m1_Sync_res n_op n_h)" 
        using assum sync_res_ex_almost_mono by metis
      then show "n_op \<in> set n_h" using assum by(auto dest: inv_uop_historyD)
    qed
  next
    fix op::"'uop" 
    fix sid pr h
    assume assum: "inv_uop_history s" "m1_B_sync sid pr op h s s'"
    show "inv_uop_history s'"
    proof(rule inv_uop_historyI)
      fix p b n_op n_h
      assume asm: "sync_res_ex s' p b (m1_Sync_res n_op n_h)"
      then have "sync_req_ex s pr sid (m1_Sync_req op h)"
        using assum by(auto dest!: sync_req_ex_Backup)
      then show "n_op \<in> set n_h" 
        apply(cases "pr = p \<and> sid = b")
         apply auto
        using assum
        apply(auto simp add: m1_defs) using asm inv_uop_historyD
        using assum(2) sync_res_ex_Backup' apply fastforce
        by (metis asm assum(2) inv_uop_history_def sync_res_ex_Backup')+
    next
      fix p b n_op n_h
      assume "sync_req_ex s' p b (m1_Sync_req n_op n_h)"
      then show "n_op \<in> set n_h" 
        using \<open>inv_uop_history s\<close> \<open>m1_B_sync sid pr op h s s'\<close>
        by (auto simp add:  dest!: sync_req_ex_almost_mono 
             dest: inv_uop_historyD)
    qed
  qed (auto elim: sync_res_ex_almost_mono sync_req_ex_almost_mono 
            intro!: inv_uop_historyI dest: inv_uop_historyD)
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsubsection \<open>@{term inv_history_backup}\<close>
text \<open>The variable storing the latest history received by backup b from server p, i.e., hist s b p,
is [], if p does not believe itself to be the primary server. The reason is simple: if that is the
case, then p will not send out a sync request, and hist s b p will never get overwritten from its
initial value [].\<close>
definition inv_history_backup where
  "inv_history_backup s \<equiv> (\<forall> p b pr . pr \<in> live s (Server p) \<and> pr < p \<and> p < b \<longrightarrow> hist s b p = [])"

lemma inv_history_backupI:
  "\<lbrakk>\<And> p b pr . \<lbrakk>pr \<in> live s (Server p); pr < p; p < b\<rbrakk> \<Longrightarrow> hist s b p = []\<rbrakk>\<Longrightarrow> inv_history_backup s"
  by(auto simp add: inv_history_backup_def)

lemma inv_history_backupD:
  "\<lbrakk>inv_history_backup s; pr \<in> live s (Server p); pr < p; p < b\<rbrakk> \<Longrightarrow> hist s b p = []"
  by(auto simp add: inv_history_backup_def)

lemma Inv_inv_history_backup: 
  "Inv m1 inv_history_backup"
proof(rule Invariant_rule_Inv[where J="(\<lambda> s. inv_alive s \<and> inv_sync_prim s)"],
      auto intro!: multiple_Inv)  fix s0::"'uop m1_state"
  assume "init m1 s0"
  then show "inv_history_backup s0" 
    by(auto simp add: inv_history_backup_def m1_defs sync_ex_defs)
next
  fix s::"'uop m1_state" 
  fix e s'
  assume asm: "m1: s\<midarrow>e\<rightarrow> s'" "reach m1 s" "inv_history_backup s" "inv_sync_prim s" "inv_sync_prim s'"
"inv_alive s'"
  then show "inv_history_backup s'" using \<open>m1: s\<midarrow>e\<rightarrow> s'\<close> 
  proof (auto simp add: m1_def)
    fix op::"'uop" 
    fix sid cid op h h'
    assume assum: "inv_history_backup s" "m1_P_req sid cid op h' s s'"
    have trivial_case: "\<And>p b . hist s' b p = hist s b p"
      using assum(2) by(auto simp add: m1_defs)
    show "inv_history_backup s'"
    proof(rule inv_history_backupI)
      fix p b pr
      assume "pr \<in> live s' (Server p)" "pr < p" "p < b"
      then show "hist s' b p = []"
        using \<open>inv_history_backup s\<close> assum
        by(auto simp add: trivial_case elim!: inv_history_backupD elim: live_mono)
    qed
  next (*B1_P_res*)
    fix op::"'uop" 
    fix sid cid op h h'
    assume assum: "inv_history_backup s" "m1_P_res sid cid op h s s'"
    have sid_leq: "\<And>sid' . \<lbrakk>sid' \<in> live s (Server sid); \<not>singleton_live s sid\<rbrakk> \<Longrightarrow> sid' \<ge> sid"
      using assum(2) apply(auto dest!: sync_ex_Server_res)
      using assum(2) \<open>inv_sync_prim s\<close> apply(auto simp add: m1_defs dest!: inv_sync_primD)
      using asm(4) inv_sync_primD(1) by blast
    show "inv_history_backup s'"
    proof(rule inv_history_backupI)
      fix p b pr
      assume "pr \<in> live s' (Server p)" "pr < p" "p < b"
      then show "hist s' b p = []"
        using assum(1,2) apply(cases "singleton_live s sid")
        subgoal 
          by(auto intro: live_mono dest!: inv_history_backupD, auto simp add: m1_defs dest: singleton_liveD) 
        using sid_leq assum(1,2) by(fastforce simp add: m1_defs dest!: inv_history_backupD)
    qed
  next (*B1_B_sync*)
    fix op::"'uop" 
    fix sid pr op h h'
    assume assum: "inv_history_backup s" "m1_B_sync sid pr op h s s'"
    show "inv_history_backup s'"
    proof(rule inv_history_backupI)
      fix p b pr
      assume "pr \<in> live s' (Server p)" "pr < p" "p < b"
      then show "hist s' b p = []"
        using assum(1,2) apply(auto simp add: m1_defs live_geq_def dest!: inv_history_backupD) (*takes a few sec*)
        using assum(1) inv_history_backupD apply blast
               apply (meson asm(4) assum(2) inv_sync_primD(1) leD sync_ex_Backup)+
        using assum(1) inv_history_backupD by blast+
    qed
  qed (auto intro!: inv_history_backupI intro: live_mono dest!: inv_history_backupD, auto simp add: m1_defs)
qed(auto intro: Inv_inv_sync_prim Inv_inv_alive)


(**************************************************************************************************)
(**************************************************************************************************)
subsubsection \<open>@{term inv_own_hist}\<close>
text \<open>If a backup b has sent a reply to a primary p, and that primary is believed to be alive, then
the last history received from p is identical to b's own history.\<close>

definition inv_own_hist where
  "inv_own_hist s \<equiv> 
  \<forall>p b m . sync_res_ex s p b m \<and> p \<in> live s (Server b) 
       \<longrightarrow> hist s b p = hist s b b"

lemma inv_own_histI:
 "\<lbrakk>\<And>p b m. \<lbrakk>sync_res_ex s p b m ; p \<in> live s (Server b)\<rbrakk> \<Longrightarrow> hist s b p = hist s b b\<rbrakk> 
  \<Longrightarrow> inv_own_hist s"
  by(auto simp add: inv_own_hist_def)

lemma inv_own_histD:
  "\<lbrakk>inv_own_hist s; sync_res_ex s p b m; p \<in> live s (Server b)\<rbrakk> \<Longrightarrow> hist s b p = hist s b b"
  by(auto simp add: inv_own_hist_def)

lemma inv_own_hist_ident: 
  "\<lbrakk>inv_own_hist s; hist s' = hist s; live s' = live s; 
    \<And>p b m . sync_res_ex s' p b m \<Longrightarrow> sync_res_ex s p b m\<rbrakk> \<Longrightarrow> inv_own_hist s'"
  by(auto simp add: prim_def intro!: inv_own_histI dest!: inv_own_histD)

lemma inv_own_hist_self: "p = b \<Longrightarrow> hist s b p = hist s b b"
  by blast

lemma inv_own_hist_Backup_sync:
  assumes "m1_B_sync sid pr op h s s'" 
          "sync_res_ex s' p b m" "p \<in> live s' (Server b)"
          "inv_own_hist s" "inv_sync_backup s" "inv_sync_backup s'"
        shows "hist s' b p = hist s' b b"
proof(cases "sid = b")
  case sid_b: True
  then have "sync_res_ex s' pr b (m1_Sync_res op h)"
    using assms(1) by (auto simp add: m1_defs intro: sync_res_set_exI)
  then have p_geq_pr: "p \<ge> pr" using assms(3,6) by (auto elim: inv_sync_backupD)
  then show ?thesis 
  proof(cases "p=pr")
    case True
    then show ?thesis using assms(1) sid_b by (auto simp add: m1_defs)
  next
    case p_neq_pr: False (* p \<noteq> pr *)
    then have "p > pr" using p_geq_pr by(auto)
    moreover have "pr \<ge> p" 
      using assms(1,2,6) by (auto simp add: sid_b m1_defs live_geq_def elim: inv_sync_backupD dest:)
    ultimately show ?thesis by auto
  qed
next
  case False (* sid \<noteq> b *)
  then have "sync_res_ex s p b m" "p \<in> live s (Server b)"
    using assms(1-3) by (auto simp add: m1_defs sync_res_ex_def)
  then show ?thesis
    using assms(1,4) False by (auto simp add: m1_defs dest!: inv_own_histD)
qed

lemma Inv_inv_own_hist: "Inv m1 inv_own_hist"
proof(rule Invariant_rule_Inv[where J="(\<lambda> s. inv_sync_backup s \<and> inv_sync_prim s)"],
      auto intro!: multiple_Inv)
  fix s0::"'uop m1_state"
  assume "init m1 s0"
  then show "inv_own_hist s0" 
    by(auto simp add: inv_own_hist_def sync_res_ex_def m1_defs)
next
  fix s::"'uop m1_state" 
  fix e s'
  assume asm: "m1: s\<midarrow>e\<rightarrow> s'" "reach m1 s" "inv_own_hist s" "inv_sync_backup s" "inv_sync_backup s'" 
"inv_sync_prim s" "inv_sync_prim s'" 
  then show "inv_own_hist s'" using \<open>m1: s\<midarrow>e\<rightarrow> s'\<close> 
  proof (auto simp add: m1_def)
    fix sid cid op h h'
    assume "m1_P_req sid cid op h' s s'" "inv_own_hist s"
    then show "inv_own_hist s'"  
      by (auto intro!: inv_own_histI simp add: m1_defs sync_res_ex_def live_geq_def dest: inv_own_histD)
  next
    fix sid cid op h
    assume "m1_P_res sid cid op h s s'" "inv_own_hist s" "inv_sync_prim s"
    then show "inv_own_hist s'"  
(* *** takes a few seconds *** *)
      apply (auto intro!: inv_own_histI simp add: m1_defs sync_res_ex_def dest: inv_own_histD)
      apply(auto dest!: collect_res_sync_res_ex inv_sync_primD simp add: sync_ex_def) (*takes a few sec*)
      using antisym asm(6) inv_sync_primD sync_set_exI inv_own_histD sync_res_set_exI
      by (metis (no_types, lifting) list.sel(2) list.set_sel(2))+
  next
    fix sid pr op h
    assume "m1_B_sync sid pr op h s s'" "inv_own_hist s" "inv_sync_backup s" "inv_sync_backup s'"
    then show "inv_own_hist s'"  
      by (auto intro: inv_own_histI inv_own_hist_Backup_sync)
  next
    fix agt sid livesids
    assume "m1_Detect_failure agt sid s s'" "inv_own_hist s" 
    then show "inv_own_hist s'"  
      by(auto intro!: inv_own_histI simp add: m1_defs sync_res_ex_def remove_def dest!: inv_own_histD)
  qed(auto elim!: inv_own_hist_ident sync_res_ex_almost_mono,auto simp add: m1_defs)
qed(auto intro: Inv_inv_sync_backup Inv_inv_sync_prim) 

(**************************************************************************************************)
(**************************************************************************************************)
subsubsection \<open>@{term inv_order}\<close>
text\<open>This invariant ensures that histories that are in the local states and in the environment
conform to an order: those that propagate through the network earlier are a prefix of those which
propagate later. This allows us later to show in the lemma @{term backup_consistency} that the history
stored at the primary is a prefix of the history of the backups (at least once a sync is complete).\<close>

text\<open>Projects messages down to the history that they contain\<close>
fun extrh :: "'uop m1_sync \<Rightarrow> 'uop list" where
  "extrh (m1_Sync_req op h) = h"
| "extrh (m1_Sync_res op h) = h"

abbreviation extr where
  "extr buf s a b \<equiv> map extrh (buf s a b)"

text\<open>Creates the concatenation of histories stored in local states and channels between two servers.
Note that histories "travel" from right to left. This means that a new history will be put into
spend s p by the primary server and then get propagated to the left through the different channels and
the local state of the backup server.\<close>

definition hist_list_res :: "'uop m1_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'uop list list" where
  "hist_list_res s p b \<equiv> 
  (hist s p b) #
 (extr ssibuf s b p) @ (extr sschan s b p) @ (extr ssobuf s b p) 
  @ [hist s b p]"

definition hist_list_req :: "'uop m1_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'uop list list" where
  "hist_list_req s p b \<equiv> 
  (hist s b p) #
 (extr ssibuf s p b) @ (extr sschan s p b) @ (extr ssobuf s p b) 
  @ [spend s p]"

lemmas hist_list_defs = hist_list_res_def hist_list_req_def


text\<open>@{term inv_order}: The histories stored in the local states (@{term "spend s p"}) of a primary server p and (@{term "hist s b"})
of a backup server b, as well as the histories contained in the messages between them, are ordered:
a history in this order that is "further along" is a prefix of a history "further behind".
The first part, saying that the histories are ordered for sync requests, are needed for the backup 
event: when a backup overwrites its history with a new history by the same primary, it is an extension
of the existing stored history.
The second part, saying that histories are ordered for sync responses, is needed for the central 
property to be proven: that whenever the primary server sends out a reply to a client, this reply
is a prefix of the history stored by the backups.\<close>
definition inv_order where
  "inv_order s \<equiv> \<forall> p b . p < b \<and> alive s b \<and> alive s p
  \<longrightarrow> sorted_wrt prefix (hist_list_res s p b) \<and> sorted_wrt prefix (hist_list_req s p b)"

lemma inv_orderI: 
  "\<lbrakk>\<And>p b . \<lbrakk>p < b; alive s b; alive s p\<rbrakk> 
    \<Longrightarrow> sorted_wrt prefix (hist_list_res s p b); 
    \<And>p b . \<lbrakk>p < b; alive s b; alive s p\<rbrakk> 
    \<Longrightarrow> sorted_wrt prefix (hist_list_req s p b)\<rbrakk> 
  \<Longrightarrow> inv_order s"
  by(auto simp add: inv_order_def)

lemma inv_orderD: 
  "\<lbrakk>inv_order s; p < b; alive s b; alive s p\<rbrakk> 
  \<Longrightarrow> sorted_wrt prefix (hist_list_res s p b)"
  "\<lbrakk>inv_order s; p < b; alive s b; alive s p\<rbrakk> 
  \<Longrightarrow> sorted_wrt prefix (hist_list_req s p b)"
  by(auto simp add: inv_order_def)

lemma inv_order_req: 
  assumes "inv_order s"
    "\<And>p b . \<lbrakk>p < b; alive s' b; alive s' p\<rbrakk> 
  \<Longrightarrow> hist_list_res s' p b = hist_list_res s p b"
    "\<And>p b . \<lbrakk>p < b; alive s' b; alive s' p\<rbrakk> 
  \<Longrightarrow> sorted_wrt prefix (hist_list_req s' p b)" 
    "\<And>p b . \<lbrakk>p < b; alive s' b; alive s' p\<rbrakk> 
  \<Longrightarrow> alive s b"
    "\<And>p b . \<lbrakk>p < b; alive s' b; alive s' p\<rbrakk> 
  \<Longrightarrow> alive s p"
  shows "inv_order s'"
  using assms by(auto simp add: inv_order_def)

lemma inv_order_res: 
  "\<lbrakk>inv_order s;
    \<And>p b . \<lbrakk>p < b; alive s' b; alive s' p\<rbrakk> \<Longrightarrow> sorted_wrt prefix (hist_list_res s' p b);
    \<And>p b . \<lbrakk>p < b; alive s' b; alive s' p\<rbrakk> \<Longrightarrow> hist_list_req s' p b = hist_list_req s p b;
    \<And>p b . \<lbrakk>p < b; alive s' b; alive s' p\<rbrakk> \<Longrightarrow> alive s b;
    \<And>p b . \<lbrakk>p < b; alive s' b; alive s' p\<rbrakk> \<Longrightarrow> alive s p\<rbrakk> 
  \<Longrightarrow> inv_order s'"
  by(auto simp add: inv_order_def)

lemma inv_order_id: 
  assumes "inv_order s" and "\<And>p b . \<lbrakk>p < b; alive s b; alive s p\<rbrakk>  
                              \<Longrightarrow> hist_list_res s' p b = hist_list_res s p b" 
                        and "\<And>p b . \<lbrakk>p < b; alive s b; alive s p\<rbrakk> 
                              \<Longrightarrow> hist_list_req s' p b = hist_list_req s p b" 
                        and "\<And>p b . \<lbrakk>p < b; alive s' b\<rbrakk> \<Longrightarrow> alive s b" 
                        and "\<And>p b . \<lbrakk>p < b; alive s' p\<rbrakk> \<Longrightarrow> alive s p" 
  shows "inv_order s'"
  using assms by (auto intro!: inv_orderI dest: inv_orderD)


(**************************************************************************************************)
text\<open>Rules for putting proof goals in the right form\<close>

lemma sorted_prefix_id:
"\<lbrakk>sorted_wrt prefix (hist_list_res s p b); hist_list_res s' p b = hist_list_res s p b\<rbrakk> 
\<Longrightarrow> sorted_wrt prefix (hist_list_res s' p b)"
  by simp

lemma sorted_prefix_app_eq:
  assumes "sorted_wrt prefix (hist_list_req s p b)" "hist_list_req s p b = sb # li @ lc @ lo @ [sp]" 
    "hist_list_req s' p b = (sb # li @ lc @ lo @ [sp', sp'])" "prefix sp sp'" 
  shows "sorted_wrt prefix (hist_list_req s' p b)"
  using sorted_prefix_app assms by metis


lemma sorted_prefix_rm_eq:
  assumes "sorted_wrt prefix (hist_list_res s p b)" "hist_list_res s p b = sb # h # li @ lc @ lo @ [sp]" 
    "hist_list_res s' p b = (h # li @ lc @ lo @ [sp])" 
  shows "sorted_wrt prefix (hist_list_res s' p b)"
  using sorted_prefix_rm assms by metis

lemma sorted_prefix_empty_but_end:
  assumes "hist_list_req s' p b = (e # li @ lc @ lo @ [sp])" "e = []" "li = []" "lc = []" "lo = []"
  shows "sorted_wrt prefix (hist_list_req s' p b)"
  using assms by auto

(**************************************************************************************************)
text\<open>Hard cases of proving @{term inv_order}\<close>

lemma m1_B_sync_inv: 
  assumes "inv_order s" "m1_B_sync sid pr op h s s'" 
          "inv_sync_prim s" "inv_alive s" "inv_upd_req s" "inv_history_backup s"
          "inv_sync_prim s'" "inv_alive s'" "inv_upd_req s'" "inv_history_backup s'"
    shows "inv_order s'"
proof-
  have "sync_ex s pr sid (m1_Sync_req op h)" using assms(2) by(intro sync_ex_Backup)
  have sync_res_pr_sid: "sync_res_ex s' pr sid (m1_Sync_res op h)" 
    using assms(2) by(intro sync_res_ex_Backup)
  then show ?thesis proof (auto intro!: inv_orderI)
    fix p b
    assume assm: "p < b" "alive s' b" "alive s' p"
    then have "sorted_wrt prefix (hist_list_req s p b)"
      using \<open>inv_order s\<close> assms(2) by(auto elim!: inv_orderD dest: live_mono)
    have sorted_s_res: "sorted_wrt prefix (hist_list_res s p b)"
      using assm \<open>inv_order s\<close> assms(2) by(auto elim!: inv_orderD dest: live_mono)

    show "sorted_wrt prefix (hist_list_res s' p b)"
    proof(cases "pr = p \<and> sid = b")
      case pr_sid_def: True

      then have "prefix (hist s b p) h" using \<open>sorted_wrt prefix (hist_list_req s p b)\<close>
        using assms(2) by(auto simp add: hist_list_defs m1_defs)

      then show ?thesis 

        using pr_sid_def assms(1,2) \<open>p < b\<close> apply (auto simp add: m1_B_sync_def)
        using \<open>sorted_wrt prefix (hist_list_res s p b)\<close>
        apply(simp only: hist_list_defs)
        apply - apply(erule sorted_wrt_append_last)
        by auto
    next
      case False
      have "hist_list_res s' p b = hist_list_res s p b" 
        apply(auto intro!: l2_ident simp add: hist_list_res_def)
        using assms(2) apply (auto simp add: m1_B_sync_def live_geq_def)
        using False \<open>p < b\<close> apply auto 
        apply(cases "b = pr")
        using assm assms inv_alive_contradict inv_sync_primD nat_less_le order.strict_trans1 sync_exI(3) 
        by auto
      then show ?thesis by (simp add: sorted_s_res)
      qed
  next
    fix p b
    assume assm: "p < b" "alive s' b" "alive s' p"
    then have sorted_s_req: "sorted_wrt prefix (hist_list_req s p b)"
      using \<open>inv_order s\<close> assms(2) by(auto elim!: inv_orderD dest: live_mono)
    show "sorted_wrt prefix (hist_list_req s' p b)" 
    proof(cases "pr = p \<and> sid = b")
      case True
      then show ?thesis 
        using assms(1,2) \<open>p < b\<close> apply (auto simp add: m1_B_sync_def)
        using \<open>sorted_wrt prefix (hist_list_req s p b)\<close>
        apply(simp only: hist_list_defs)
        apply - apply(erule sorted_wrt_fwd_second)
        by auto
    next
      case pr_neq_p_or_sid_neq_b: False
      have "pr \<in> live s (Server sid)" using assms(2) by(auto simp add: m1_defs)
      then have "pr \<le> p" "pr < sid" using \<open>inv_sync_prim s'\<close> sync_res_pr_sid \<open>alive s' p\<close> \<open>inv_alive s'\<close> 
         apply(auto dest!: inv_aliveD dest: inv_sync_primD simp add: sync_ex_defs)
        using m1_B_sync_live \<open>m1_B_sync sid pr op h s s'\<close> apply fast+
        using \<open>sync_ex s pr sid (m1_Sync_req op h)\<close> assms(3) inv_sync_prim_def by blast+
      have "pr \<le> sid" using assms(2) \<open>sync_ex s pr sid (m1_Sync_req op h)\<close> assms(3) assms(4) 
        inv_alive_contradict inv_sync_primD by fastforce
      then have "alive s' sid" using assms(2) by(auto simp add: m1_defs live_geq_def)
      then have sync_p_leq_sid: "\<And> m . sync_req_ex s' p b m \<Longrightarrow> p \<le> sid" 
        subgoal for m
          using \<open>inv_sync_prim s'\<close>  apply (auto elim!: inv_sync_primD[of s' p b m ])
           apply(auto simp add: sync_ex_def) 
          using \<open>inv_alive s'\<close> by(auto dest!: inv_aliveD) done
      then show ?thesis
      proof(cases "sid = b")
        case sid_eq_b: True 
        then have "pr \<noteq> p" using pr_neq_p_or_sid_neq_b by simp
        then have "hist_list_req s' p b = hist_list_req s p b" 
          apply(auto intro!: l2_ident simp add: hist_list_defs)
          using assms(2) apply (auto simp add: m1_B_sync_def)
          using sid_eq_b \<open>p < b\<close> by blast+
        then show ?thesis
          using assm \<open>inv_order s\<close> assms(2) by(auto elim!: inv_orderD dest: live_mono)
      next
        case sid_neq_b: False
        then show ?thesis
        proof(cases "sid = p")
          case sid_eq_p: True (*I think this is the interesting case*)
          then have "pr \<in> live s' (Server sid)" 
            using assm assms(2) by(auto simp add: m1_defs live_geq_def)

          then have "hist s' b p = []" (*needs invariant inv_history_backup*)
            using \<open>inv_history_backup s'\<close> apply- apply(erule inv_history_backupD)
            using \<open>pr \<in> live s' (Server sid)\<close> \<open>pr < sid\<close> \<open>sid = p\<close> \<open>p < b\<close>
            by auto
          from sid_eq_p have "\<And> m . sync_req_ex s' p b m \<Longrightarrow> False" 
            apply(cases "alive s' pr")
            subgoal for m
              using \<open>pr < sid\<close> using \<open>inv_sync_prim s'\<close>  apply (auto dest!: inv_sync_primD(2)[of s' p b m ])
              apply(auto simp add: sync_ex_def) 
              by (meson assms(7) assms(8) inv_alive_partialD inv_sync_prim_def leD sync_ex_def)
            using \<open>pr \<le> p\<close> \<open>pr < sid\<close> pr_neq_p_or_sid_neq_b sid_neq_b apply auto
            using \<open>pr \<in> live s (Server sid)\<close> assms(2) assms(3) inv_sync_prim_def leD sync_ex_almost_mono sync_ex_def
            by metis
          moreover have "\<And> m . sync_res_ex s' b p m \<Longrightarrow> False" 
            using \<open>p < b\<close> \<open>inv_sync_prim s'\<close> by(auto dest!: inv_sync_primD(2) simp add: sync_ex_def)
          ultimately have "ssibuf s' p b = []" "ssobuf s' p b = []" "sschan s' p b = []" 
            apply(auto simp add: sync_ex_defs) by (meson last_in_set m1_sync.exhaust)+
          then show ?thesis
            apply(intro sorted_prefix_empty_but_end)
            using \<open>hist s' b p = []\<close> by(auto simp add: hist_list_defs) 
        next
          case sid_neq_p: False
          then have hist_eq: "hist_list_req s' p b = hist_list_req s p b"
            using assms(2) pr_neq_p_or_sid_neq_b by(auto simp add: hist_list_defs m1_defs)
          show ?thesis 
            using assms(1) assm apply(simp add: hist_eq) apply(erule inv_orderD) 
            using assms(2) by (auto dest: live_mono)
        qed
        qed
    qed
  qed
qed

lemma inv_order_m1_P_req:
  assumes "inv_order s" "m1_P_req p cid op h' s s'" "p < b" "alive s' b"
      "inv_alive s"
  shows "sorted_wrt prefix (hist_list_req s' p b)"
proof-
  have "prefix (spend s p) h'"
    using assms(2) by(auto simp add: m1_defs hist_list_defs cond_app_def)
  moreover have "alive s p" 
    using assms(2) \<open>inv_alive s\<close> by(auto simp add: m1_defs hist_list_defs dest: inv_aliveD)
  moreover have "extr ssobuf s' p b = extr ssobuf s p b @ [h']"
    using assms(2,3) apply(auto simp add: m1_defs hist_list_defs live_geq_def) 
    using \<open>alive s p\<close> \<open>inv_alive s\<close> \<open>alive s' b\<close> by(auto elim: inv_aliveD)
  ultimately show ?thesis
    using assms(1,3) apply- apply(drule inv_orderD(2)[of _ p b]) apply auto 
    subgoal using assms(2,4) live_mono(1) by(auto simp add: m1_defs)
    apply(erule sorted_prefix_app_eq)
    apply auto
    apply(auto simp add: hist_list_req_def)
    using assms(2) by(auto simp add: m1_defs)
qed

lemma inv_order_m1_P_res:
  assumes "inv_order s" "m1_P_res p cid op h s s'" "p < b" "alive s' b"
      "inv_alive s"
  shows "sorted_wrt prefix (hist_list_res s' p b)"
proof-
  have "alive s p" 
    using assms(2) \<open>inv_alive s\<close> by(auto simp add: m1_defs hist_list_defs dest: inv_aliveD)
  have "alive s b" using assms by(auto elim!: live_mono)
  then have "b \<in> live s (Server p)" using \<open>inv_alive s\<close> inv_aliveD by blast
  then show ?thesis apply-
    apply(rule sorted_prefix_rm_eq[of s])
    subgoal using assms(1,2,3,4) live_mono(2) \<open>alive s b\<close> \<open>alive s p\<close> by(auto elim!: inv_orderD)
    apply(auto simp add: hist_list_res_def)
    using assms(2-3) by(auto simp add: m1_defs dest!: collect_resD(1))
qed


lemma Inv_inv_order: 
  "Inv m1 inv_order"
proof(rule Invariant_rule_Inv[where 
      J="(\<lambda> s. inv_alive s \<and> inv_sync_prim s \<and> inv_upd_req s \<and> inv_history_backup s)"],
      auto intro!: multiple_Inv)
  fix s0::"'uop m1_state"
  assume "init m1 s0"
  then show "inv_order s0" 
    by(auto simp add: inv_order_def m1_defs hist_list_defs)
next
  fix s::"'uop m1_state" 
  fix e s'
  assume asm: "m1: s\<midarrow>e\<rightarrow> s'" "reach m1 s" "inv_order s" "inv_sync_prim s" "inv_sync_prim s'"
    "inv_upd_req s" "inv_alive s"
          "inv_alive s'" "inv_upd_req s'" "inv_history_backup s" "inv_history_backup s'"
  then show "inv_order s'" using \<open>m1: s\<midarrow>e\<rightarrow> s'\<close> 
  proof (auto simp add: m1_def)
    fix sid cid op h h'
    assume assm: "inv_order s" "m1_P_req sid cid op h' s s'" "inv_alive s"
    have hist_list_req_id: "\<And> x y . x \<noteq> sid \<Longrightarrow> hist_list_req s' x y = hist_list_req s x y" 
      using assm(2) by(auto simp add: m1_defs hist_list_defs)
    show "inv_order s'" 
    proof(rule inv_order_req)
      fix x y
      assume "x < y" "alive s' x" "alive s' y"
      show "hist_list_res s' x y = hist_list_res s x y" 
        using assm(2) apply(auto simp add: m1_defs hist_list_defs)
        using \<open>x < y\<close> order.asym by blast
    next
      fix x y (*hist_list_req, harder case *)
      assume asssm: "x < y" "alive s' x" "alive s' y"
      have "upd_req_ex s cid sid (m1_Upd_req op)" 
        using assm(2) by(auto simp add: m1_defs upd_req_ex_def)
      then show "sorted_wrt prefix (hist_list_req s' x y)"
        apply(cases "x = sid")
        subgoal 
          apply(cases "x \<le> y")
            subgoal
              using assm apply (auto elim!: inv_order_m1_P_req simp add: \<open>x < y\<close>)
              apply(auto simp add: m1_P_req_def)
              using \<open>x < y\<close> apply simp
              using \<open>alive s' y\<close> by auto
            subgoal 
              using \<open>alive s' y\<close>  assm(2) m1_P_req_live_geq using asssm(1) by fastforce
        done
        subgoal using assm asssm 
          by(auto dest: inv_orderD(2) intro: live_mono simp add: hist_list_req_id)
        done
    qed(auto intro: assm(1-2) live_mono)
  next 
    fix sid cid op h 
    assume assm: "inv_order s" "m1_P_res sid cid op h s s'" "inv_alive s"
    then show "inv_order s'"
      apply(auto elim!: inv_order_res)
      subgoal for p b
        apply(cases "sid = p")
        subgoal
          using assm by (auto elim!: inv_order_m1_P_res)
        (*sid \<noteq> p*)
        apply(rule sorted_prefix_id[of s])
          using assm(1) apply-apply(drule inv_orderD)
              apply(auto simp add: hist_list_res_def m1_defs)
          by (metis assm(2) asm(4) inv_sync_primD(1) leD neq_iff singleton_liveD sync_ex_Server_res)
          apply(auto simp add: hist_list_defs m1_defs)
        by(metis asm(4) assm(2) inv_sync_prim_def leD less_imp_neq singleton_liveD sync_ex_Server_res)+
  next 
    fix b p op h 
    assume "inv_order s" and "m1_B_sync b p op h s s'" 
          "inv_sync_prim s" "inv_alive s" "inv_upd_req s" "inv_history_backup s"
          "inv_sync_prim s'" "inv_alive s'" "inv_upd_req s'" "inv_history_backup s'"
    then show "inv_order s'" 
      using asm(4) by (auto intro: m1_B_sync_inv)
  next 
    fix x y type
    assume "inv_order s" and "m1_S_purge x y s s'" 
    then show "inv_order s'" 
      apply(auto intro!: inv_orderI)
      subgoal for p b
        by(drule inv_orderD, auto intro: live_mono simp only: hist_list_defs)
          (auto simp add: m1_S_purge_def elim!: sorted_wrt_may_drop_second)
      subgoal for p b
        by(drule inv_orderD(2), auto intro: live_mono simp only: hist_list_defs)
          (auto simp add: m1_S_purge_def elim!: sorted_wrt_may_drop_second)
      done
  next 
    fix sa ra type m
    assume "inv_order s" and "m1_ss_Send sa ra m s s'" 
    then show "inv_order s'" 
      by(elim inv_order_id)(auto simp add: m1_ss_Send_def hist_list_defs)
  next 
    fix sa ra type m
    assume "inv_order s" "inv_alive s" "m1_ss_Recv sa ra m s s'" 
    then show "inv_order s'" 
      by(elim inv_order_id)(auto 3 4 simp add: m1_ss_Recv_def hist_list_defs dest: inv_aliveD)
  qed (auto elim: inv_order_id simp add: remove_def hist_list_defs m1_defs) (*takes a few sec*)
qed(auto intro: Inv_inv_alive Inv_inv_sync_prim Inv_inv_upd_req Inv_inv_history_backup)


(**************************************************************************************************)
(**************************************************************************************************)
subsection \<open>Safety property: Backup consistency\<close>
text\<open>We now formulate the central safety property, formulated over both states and events. Further below, 
we derive a pure trace property, since our refinement approach is based on trace inclusion/equality.\<close>

text\<open>If a primary replies to a client, then the history sent to the client is a prefix of all histories
stored on the servers that are alive (including the primary server itself).\<close>
lemma backup_consistency:
  assumes "m1_P_res p cid op h s s'"
  and "inv_alive s" and "inv_sync_prim s" and "inv_order s" and "inv_own_hist s" 
  and "alive s b" 
shows "prefix h (hist s' b b)"
proof(cases "b = p")
  case b_p_eq[simp]: True
  have "alive s p" using assms(1) by(auto simp add: m1_P_res_def)
  have "(LEAST x. x \<in> live s (Server p)) = p"
    proof(rule Least_equality)
      show "p \<in> live s (Server p)" using \<open>alive s b\<close> by auto
    next
      fix sid'
      assume asm: "sid' \<in> live s (Server p)"
      then have "sid' \<noteq> p \<Longrightarrow> sync_ex s p sid' (m1_Sync_res op h)" 
        using assms(1) by(auto simp add: m1_defs sync_ex_defs dest!: collect_resD(1))
      then show "p \<le> sid'" using assms(3) asm by(cases "sid' \<noteq> p", auto elim: inv_sync_primD)
    qed
  then have "prim s' (Server b) = Some b" "hist s' b b = h"
    using assms(1) by(auto simp add: m1_P_res_def prim_def)
  then show ?thesis by(auto)
next
  case b_neq_p: False (*b \<noteq> p*)
  then have "ss_recv_msg s ssibuf b p (m1_Sync_res op h)" 
    using assms(1) \<open>alive s b\<close> \<open>inv_alive s\<close> 
    by(fastforce simp add: m1_defs dest!: collect_resD(1) inv_alive_contradict) 
  then have pld_ibuf: "h \<in> set (extr ssibuf s b p)" by force

  have sync_res: "sync_res_ex s p b (m1_Sync_res op h)" 
      using assms(1) apply(auto simp add: sync_res_ex_def m1_defs dest!: collect_resD)
      using \<open>ss_recv_msg s ssibuf b p (m1_Sync_res op h)\<close> by auto

  show ?thesis proof(cases "p < b")
    case True
    have "alive s p"
      by (meson assms(1) assms(2) inv_alive_mono m1_P_res_def)
    then have "sorted_wrt prefix (hist_list_res s p b)"
      using assms(4) b_neq_p True \<open>alive s b\<close> \<open>inv_alive s\<close> by(auto elim: inv_orderD dest: inv_aliveD) (*takes some seconds*)
    then have "sorted_wrt prefix ((extr ssibuf s b p)@[hist s b p])"
      using append_assoc sorted_wrt_drop_middle sorted_wrt_drop_end hist_list_defs
      proof -
        have "\<forall>as ass p. sorted_wrt p ass \<or> \<not> sorted_wrt p ((as::'a list) # ass)" (*wtf*)
          by force
        then show ?thesis
          by (metis (no_types) \<open>sorted_wrt prefix (hist_list_res s p b)\<close> hist_list_defs(1) sorted_wrt_drop_middle)
      qed
    then have prefix_hist: "prefix h (hist s b p)"
      using pld_ibuf by(auto simp add: sorted_wrt_append)
    moreover have "hist s' b b = hist s b b"
      using assms(1)  by(auto simp add: m1_defs b_neq_p) 
    moreover have "hist s b b = hist s b p" 
      using \<open>inv_own_hist s\<close> assms(1) sync_res \<open>inv_alive s\<close>
      by(auto simp add: m1_defs elim: inv_own_histD[symmetric] dest: inv_aliveD)
    ultimately show ?thesis
      by (simp add: prefix_hist)
  next
    case False
    then show ?thesis using b_neq_p \<open>inv_sync_prim s\<close> sync_res
      by(auto dest!: inv_sync_primD simp add: sync_ex_def)
  qed
qed
(******************************************************************************)
subsubsection\<open>Trace property\<close>
(******************************************************************************)
text\<open>We now derive a trace property that is similar to the above lemma @{text backup_consistency}, but only
refers to events, and not the state.\<close>
definition backup_consistent :: "'uop m1_event trace \<Rightarrow> bool" where
  "backup_consistent \<tau> \<longleftrightarrow> 
\<comment> \<open>If on a trace where a backup sync event precedes a a primary response event...\<close>
  (\<forall>p cid op h b p_b op_b h_b \<tau>1 \<tau>2. \<tau> = \<tau>1 @ [B1_B_sync b p_b op_b h_b] @ \<tau>2 @ [B1_P_res p cid op h] \<and>
\<comment> \<open>and where the backup is distinct from the primary...\<close>
  p \<noteq> b \<and>
\<comment> \<open>and where the selected backup sync event was the last to modify the history's state...\<close>
  \<not>(\<exists>p' op' h' . B1_B_sync b p' op' h' \<in> set \<tau>2) \<and> \<not>(\<exists>sid' op' h' . B1_P_res b sid' op' h' \<in> set \<tau>2) \<and>
\<comment> \<open>and the backup has not failed...\<close>
  \<not> B1_Detect_failure (Server b) b \<in> set \<tau>
\<comment> \<open>then the primary's history is a prefix of the backup's history\<close>
  \<longrightarrow> prefix h h_b)"

lemmas backup_consistentI = backup_consistent_def [THEN iffD2, rule_format]
lemmas backup_consistentE [elim] = backup_consistent_def [THEN iffD1, elim_format, rule_format]

lemma hist_alive_evt: 
  "\<lbrakk>m1: s\<midarrow>B1_B_sync b p op h\<rightarrow> s'; inv_sync_prim s'\<rbrakk> \<Longrightarrow> h = hist s' b b \<and> alive s' b"
  "p \<noteq> b \<Longrightarrow> m1: s\<midarrow>B1_P_res p cid op h\<rightarrow> s' \<Longrightarrow> hist s b b = hist s' b b"
  apply(auto simp add: m1_def)
  subgoal by(auto simp add: m1_defs)
  apply(frule sync_res_ex_Backup)
  by(auto simp add: m1_defs live_geq_def sync_ex_def dest!: inv_sync_primD(2))

lemma hist_alive_eq: 
  "\<lbrakk>m1: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'; \<forall>p' op' h'. B1_B_sync b p' op' h' \<notin> set \<tau>;
  \<forall>sid' op' h'. B1_P_res b sid' op' h' \<notin> set \<tau>; B1_Detect_failure (Server b) b \<notin> set \<tau>\<rbrakk>
\<Longrightarrow> hist s' b b = hist s b b \<and> alive s' b \<longleftrightarrow> alive s b"
  apply(induction \<tau> s' rule: trace.induct, auto)
  subgoal by(fastforce simp add: m1_defs)
  by(fastforce simp add: m1_defs live_geq_def remove_def)+

lemma m1_backup_consistency: "m1 \<Turnstile>\<^sub>E\<^sub>S Collect backup_consistent"
  apply(rule Inv_trace_property[where I="(\<lambda>s . inv_alive s \<and> inv_sync_prim s \<and> inv_order s \<and> inv_own_hist s)"])
  subgoal using Inv_inv_alive Inv_inv_sync_prim Inv_inv_order Inv_inv_own_hist by(auto intro!: InvI)
  subgoal by(auto simp add: backup_consistent_def)
  subgoal for s0 \<tau> s3 e s4
    apply(auto intro!: backup_consistentI dest!: trace_append_invert trace_consD)
    subgoal for p cid op h b p_b op_b h_b \<tau>1 \<tau>2 s1 s2
      apply(frule inv_sync_prim_trace, simp)
      apply(frule inv_sync_prim_trans[where s=s1], simp)
      by(auto dest!: hist_alive_evt hist_alive_eq[where ?b=b, where \<tau>=\<tau>2, symmetric])
        (auto simp add: m1_def elim: backup_consistency)
    done
  done

end
end
