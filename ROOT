(*******************************************************************************

  Project: Igloo Theory and Case Studies

  Module:  ROOT file for session building (Isabelle/HOL 2023)
  ID:      $Id: ROOT 152662 2020-08-06 09:54:41Z tklenze $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  build command example:
    isabelle build -v -b -d . <session/-name>
    isabelle build -v -D .

  Copyright (c) 2018-2020 Christoph Sprenger 
  Licence: LGPL

*******************************************************************************)

chapter Igloo

session Igloo = HOL +
  description \<open>Igloo Theory\<close>
  options [
    document=pdf,
    document_output="generated/igloo",
    document_variants="document:outline=/proof,/ML",
    threads=8
  ]
  sessions
    "HOL-Library"
  theories 
    Event_Systems
    Composition
    Interleaving
    Decomposition
    Event_Composition
    ENat
    EMultiset
    Preliminaries
    IO_Processes
    Event_Systems_into_IO_Processes
    IO_Separation_Logic
    IO_Processes_into_IO_Separation_Logic
    IO_Behavior
    Igloo
  document_files (in "document")
    "root.tex" "session_graph.tex"

session Igloo_Examples in "case-studies" = HOL +
  description \<open>Igloo Case Studies\<close>
  options [
    document=pdf,
    document_output="../generated/case-studies",
    document_variants="document:outline=/proof,/ML",
    threads=8
  ]
  sessions
    Igloo
  directories
    "leader-election"
    "replication"
    "security-protocols"
    "security-protocols/infrastructure"
  theories
    "leader-election/Leader_Election_0"
    "leader-election/Ring_network"
    "leader-election/Leader_Election_1"
    "leader-election/Leader_Election_2"
    "leader-election/Leader_Election_3"
    "leader-election/Leader_Election_4"
    "replication/Utils"
    "replication/Primary_Backup_1"
    "replication/Primary_Backup_2"
    "replication/Primary_Backup_3"
    "security-protocols/infrastructure/Infra"
    "security-protocols/infrastructure/Agents"
    "security-protocols/infrastructure/Keys"
    "security-protocols/infrastructure/Atoms"
    "security-protocols/infrastructure/Runs"
    "security-protocols/infrastructure/Channels"
    "security-protocols/infrastructure/Message"
    "security-protocols/infrastructure/Crypto_Algebra"
    "security-protocols/infrastructure/a0n_agree"
    "security-protocols/infrastructure/a0i_agree"
    "security-protocols/m1_auth"
    "security-protocols/m2_auth_chan"
    "security-protocols/m3_sig"
    "security-protocols/m4_sig"
    "security-protocols/m5_sig"
    "security-protocols/m6_sig"
  document_files (in "../document")
    "root.tex" "session_graph.tex"
