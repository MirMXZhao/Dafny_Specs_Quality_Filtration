// include "IOModel.i.dfy"
// include "../lib/DataStructures/LinearMutableMap.i.dfy"

// module CommitterCommitModel {
//   import opened NativeTypes
//   import opened Options

//   import opened DiskLayout
//   import opened InterpretationDiskOps
//   import opened ViewOp
//   import JC = JournalCache
//   import opened Journal
//   import opened JournalBytes
//   import opened DiskOpModel
//   import SectorType

//   import LinearMutableMap
//   // import opened StateModel
//   import opened IOModel

//   function SyncReqs2to1Iterate(
//       m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>,
//       it: LinearMutableMap.Iterator<JC.SyncReqStatus>,
//       m0: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//     : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   requires LinearMutableMap.WFIter(m, it)
//   requires LinearMutableMap.Inv(m0)
//   requires m0.contents.Keys == it.s
//   ensures LinearMutableMap.Inv(m')
//   decreases it.decreaser
//   {}

//   function {:opaque} SyncReqs2to1(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//       : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   ensures LinearMutableMap.Inv(m')
//   {}

//   lemma SyncReqs2to1Correct(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   ensures SyncReqs2to1(m).contents == JC.syncReqs2to1(m.contents)
//   {}

//   function SyncReqs3to2Iterate(
//       m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>,
//       it: LinearMutableMap.Iterator<JC.SyncReqStatus>,
//       m0: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//     : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   requires LinearMutableMap.WFIter(m, it)
//   requires LinearMutableMap.Inv(m0)
//   requires m0.contents.Keys == it.s
//   ensures LinearMutableMap.Inv(m')
//   decreases it.decreaser
//   {}

//   function {:opaque} SyncReqs3to2(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//       : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   ensures LinearMutableMap.Inv(m')
//   {}

//   lemma SyncReqs3to2Correct(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   ensures SyncReqs3to2(m).contents == JC.syncReqs3to2(m.contents)
//   {}

  // function {:opaque} WriteOutJournal(cm: CM, io: IO)
  //     : (res : (CM, IO))
  // requires io.IOInit?
  // requires CommitterModel.WF(cm)
  // requires JournalistModel.I(cm.journalist).inMemoryJournalFrozen != []
  //       || JournalistModel.I(cm.journalist).inMemoryJournal != []
  // {}

  // lemma WriteOutJournalCorrect(cm: CM, io: IO)
  // requires WriteOutJournal.requires(cm, io)
  // requires cm.superblockWrite.None?
  // ensures var (cm', io') := WriteOutJournal(cm, io);
  //   && CommitterModel.WF(cm')
  //   && ValidDiskOp(diskOp(io'))
  //   && IDiskOp(diskOp(io')).bdop.NoDiskOp?
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp)
  // {}

  // predicate writeOutSuperblockAdvanceLog(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires io.IOInit?
  // requires CommitterModel.WF(cm)
  // {}

  // lemma writeOutSuperblockAdvanceLogCorrect(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires io.IOInit?
  // requires CommitterModel.WF(cm)
  // requires writeOutSuperblockAdvanceLog(cm, io, cm', io')
  // requires cm.status == StatusReady
  // requires cm.commitStatus.CommitNone?
  // requires cm.outstandingJournalWrites == {}
  // requires JournalistModel.I(cm.journalist).inMemoryJournalFrozen == []
  // ensures CommitterModel.WF(cm')
  // ensures ValidDiskOp(diskOp(io'))
  // ensures IDiskOp(diskOp(io')).bdop.NoDiskOp?
  // ensures JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp)
  // {}

  // predicate {:opaque} writeOutSuperblockAdvanceLocation(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires io.IOInit?
  // requires CommitterModel.Inv(cm)
  // requires cm.status == StatusReady
  // requires cm.frozenLoc.Some?
  // {}

  // lemma writeOutSuperblockAdvanceLocationCorrect(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires io.IOInit?
  // requires CommitterModel.Inv(cm)
  // requires cm.status == StatusReady
  // requires cm.frozenLoc.Some?
  // requires cm.commitStatus.CommitNone?
  // requires cm.outstandingJournalWrites == {}
  // requires writeOutSuperblockAdvanceLocation(cm, io, cm', io')
  // requires JournalistModel.I(cm.journalist).inMemoryJournalFrozen == []
  // ensures CommitterModel.WF(cm')
  // ensures ValidDiskOp(diskOp(io'))
  // ensures IDiskOp(diskOp(io')).bdop.NoDiskOp?
  // ensures JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp)
  // {}

  // function {:opaque} freeze(cm: CM) : (cm': CM)
  // requires CommitterModel.WF(cm)
  // {}

  // lemma freezeCorrect(cm: CM)
  // requires CommitterModel.WF(cm)
  // requires cm.superblockWrite.None?

  // // Mostly we'll probably just do this with cm.frozenLoc == None
  // // but more generally we can do it whenever we have:
  // requires cm.status == StatusReady
  // requires cm.frozenLoc != Some(cm.superblock.indirectionTableLoc)
  // requires JournalistModel.I(cm.journalist).replayJournal == []

  // ensures var cm' := freeze(cm);
  //   && CommitterModel.WF(cm')
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       FreezeOp)
  // {}

  // function {:opaque} receiveFrozenLoc(
  //     cm: CM, loc: Location) : (cm': CM)
  // {}

  // lemma receiveFrozenLocCorrect(cm: CM, loc: Location)
  // requires CommitterModel.WF(cm)
  // requires cm.status == StatusReady
  // requires cm.isFrozen
  // requires !cm.frozenLoc.Some?
  // requires ValidIndirectionTableLocation(loc)

  // ensures var cm' := receiveFrozenLoc(cm, loc);
  //   && CommitterModel.WF(cm')
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       SendFrozenLocOp(loc))
  // {}

  // // == pushSync ==

  // function {:opaque} freeId<A>(syncReqs: LinearMutableMap.LinearHashMap<A>) : (id: uint64)
  // requires LinearMutableMap.Inv(syncReqs)
  // ensures id != 0 ==> id !in syncReqs.contents
  // {}

  // function pushSync(cm: CM) : (CM, uint64)
  // requires CommitterModel.WF(cm)
  // {}

  // lemma pushSyncCorrect(cm: CM)
  // requires CommitterModel.WF(cm)

  // ensures var (cm', id) := pushSync(cm);
  //   && CommitterModel.WF(cm')
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       if id == 0 then JournalInternalOp else PushSyncOp(id as int))
  // {}

  // // == popSync ==

  // function {:opaque} popSync(cm: CM, id: uint64) : (cm' : CM)
  // requires CommitterModel.WF(cm)
  // {}

  // lemma popSyncCorrect(cm: CM, id: uint64)
  // requires CommitterModel.WF(cm)
  // requires id in cm.syncReqs.contents
  // requires cm.syncReqs.contents[id] == JC.State1
  // ensures var cm' := popSync(cm, id);
  //   && CommitterModel.WF(cm')
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       PopSyncOp(id as int))
  // {}

  // // == AdvanceLog ==

  // predicate {:opaque} tryAdvanceLog(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires CommitterModel.WF(cm)
  // requires io.IOInit?
  // {}

  // lemma tryAdvanceLogCorrect(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires CommitterModel.Inv(cm)
  // requires io.IOInit?
  // requires cm.status.StatusReady?
  // requires tryAdvanceLog(cm, io, cm', io')
  // ensures CommitterModel.WF(cm')
  // ensures ValidDiskOp(diskOp(io'))
  // ensures IDiskOp(diskOp(io')).bdop.NoDiskOp?
  // ensures JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp)
  // {}

  // predicate {:opaque} tryAdvanceLocation(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires CommitterModel.Inv(cm)
  // requires io.IOInit?
  // requires cm.status == StatusReady
  // requires cm.frozenLoc.Some?
  // {}

  // lemma tryAdvanceLocationCorrect(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires CommitterModel.Inv(cm)
  // requires io.IOInit?
  // requires cm.status.StatusReady?
  // requires cm.frozenLoc.Some?
  // requires tryAdvanceLocation(cm, io, cm', io')
  // ensures CommitterModel.WF(cm')
  // ensures ValidDiskOp(diskOp(io'))
  // ensures IDiskOp(diskOp(io')).bdop.NoDiskOp?
  // ensures JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp)
  // {}

  // function {:opaque} writeBackSuperblockResp(
  //     cm: CommitterModel.CM) : CommitterModel.CM
  // requires CommitterModel.Inv(cm)
  // {}

  // lemma writeBackSuperblockRespCorrect(
  //     cm: CommitterModel.CM, io: IO)
  // requires CommitterModel.Inv(cm)
  // requires ValidDiskOp(diskOp(io))
  // requires IDiskOp(diskOp(io)).jdop.RespWriteSuperblockOp?
  // requires Some(io.id) == cm.superblockWrite
  // ensures var cm' := writeBackSuperblockResp(cm);
  //   && CommitterModel.WF(cm')
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io)).jdop,
  //       if cm.status.StatusReady? && cm.commitStatus.CommitAdvanceLocation? then CleanUpOp else JournalInternalOp
  //   )
  // {}
// }

