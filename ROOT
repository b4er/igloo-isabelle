(*******************************************************************************

  Project: Igloo Theory and Case Studies

  Module:  ROOT file for session building (Isabelle/HOL 2020)
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
description \<open>Igloo Theory and Case Studies\<close> 
options [
  document=pdf, document_output=generated, 
  document_variants="document:outline=/proof,/ML", 
  browser_info, threads=4, 
  quick_and_dirty
]
sessions
  "HOL-Library"
directories
  "case-studies"
  "case-studies/leader-election"
  "case-studies/replication"
  "case-studies/security-protocols"
  "case-studies/security-protocols/infrastructure"
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
  "case-studies/leader-election/Leader_Election_0"
  "case-studies/leader-election/Ring_network"
  "case-studies/leader-election/Leader_Election_1"
  "case-studies/leader-election/Leader_Election_2"
  "case-studies/leader-election/Leader_Election_3"
  "case-studies/leader-election/Leader_Election_4"
  "case-studies/replication/Utils"
  "case-studies/replication/Primary_Backup_1"
  "case-studies/replication/Primary_Backup_2"
  "case-studies/replication/Primary_Backup_3"
  "case-studies/security-protocols/infrastructure/Infra"
  "case-studies/security-protocols/infrastructure/Agents"
  "case-studies/security-protocols/infrastructure/Keys"
  "case-studies/security-protocols/infrastructure/Atoms"
  "case-studies/security-protocols/infrastructure/Runs"
  "case-studies/security-protocols/infrastructure/Channels"
  "case-studies/security-protocols/infrastructure/Message"
  "case-studies/security-protocols/infrastructure/Crypto_Algebra"
  "case-studies/security-protocols/infrastructure/a0n_agree"
  "case-studies/security-protocols/infrastructure/a0i_agree"
  "case-studies/security-protocols/m1_auth"
  "case-studies/security-protocols/m2_auth_chan"
  "case-studies/security-protocols/m3_sig"
  "case-studies/security-protocols/m4_sig"
  "case-studies/security-protocols/m5_sig"
  "case-studies/security-protocols/m6_sig"
document_files
  "root.tex" "session_graph.tex"


