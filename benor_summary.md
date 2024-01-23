properties
==========
-- decide in 1 round if everyone suggests one value
-- everyone decides the same value
-- if some party decides in round r then all parties decide by r+1


environment strats
==================
-- partition inputs randomly or always give 1/2 and 1/2
-- only deliver messages per partiton
    --> give the rest at the end of the round
    --> arbitrary delay on the messages
-- deiver messages by arbitrary partition
    --> give the rest at the end of the round
    --> arbitrary delay
-- deliver all messages in just some random order
-- some subset execute the full round and then the rest
    * specifically some subset the size of an important threshold
    -- do arbitrarily for every stage of a round


Current Environments
====================

set { wrong adv rounds, censoring some parties, deliver by partition only, deliver all messages in a round, don't deliver in expected order }

selective message deliver:
    -- censor parties                                   (1)
    -- only by partition                                     (2) 
    -- shuffle all to all                                         (3)

rounds:
    -- deliver all r before r+1                              (2)  (3)
    -- deliver arbitrarily in later rounds              (1)
    -- crupt messages of different rounds               (1)

cruptions
    -- all honest                                                 (3) 
    -- byzantine                                        (1)  (2)
    -- crash faults         

structure
    -- go by message rounds                             (1)  (2)
    -- deliver messages without round consideration     


(1) benOrEnvRandomRound  -- { wrong adv rounds, censor some, don't always deliver all }
-----------------------
-- randomly chooses party inputs but no partition information
-- creates a pair of parties to censor
-- in 50 rounds:
    > for all crupt: generate 10 messages with arb round number in [r-2, r-1, r, r+1, r+2] for all parties
    > randomly choose a threshold `f` for [ (3, rqDeliverChoice c f), (1, rqDeliverAll c) ] exclude censored
    > flip a coin: deliver messages between censored parties

(2) benOrEnvByPartition -- { partition delivery of msgs, but all r delivered before r+1 }
-----------------------
-- create a partition (pT, pF) for T/F input
-- in r rounds:
    > give pT One(T) / pF One(F)
    > for p in a partition: give p One(arbitrary)
    > for crupts: generate One(arbitrary)
    > deliver all One(*)
    > give pT TwoD(T) and Twos / pf TwoD(F) and Twos
    > for crupts: generate Two()
    > for crupts: generate TwoD(*)
    > for p in a partition: give p TwoD(arbitrary)
    > deliver all Two() and TwoD(*)

(3) benOrEnvAllHonestShuffle -- { 1/2 partition, shuffle deliver all }
----------------------------
-- ASSUME: 10 parties
-- create size 5 partition pF and pT (1/2)
-- in r rounds:
    > deliver all One(*) in random order
    > deliver all Two() and TwoD(*) in random order
    > if all parties output some value: break loop
-- return last round a party decided in 
TODO: do both crupt and all honest

(4) benOrEnvAllHonestTestOutcome -- { idntical and removed }
--------------------------------
PARAMS: pidsT, pidsF
__otherwise IDENTICAL to (3) benOrEnvAllHonestShuffle__

(5) benOrEnvDeliverLoop
-----------------------
TODO: _Not used by any property_
-- no crupt party messages
-- whileM_ (runqueue isn't empty)
    * deliver some random index
TODO: likely this never terminates because loop is never empty, create a stop condition when import runs out??


Properties
==========

(1) propBenOrSafety
-------------------
-- parties between 10 and 15
-- crupt up to t
* run __(2) benOrEnvByPartition__
* pre (at least 1 party decides)
* assert (only 1 decided value)
### propBenOrSafety{CCC,CCS,...,SSS}

(2) propBenOrSucceedRound
-------------------------
ASSUME: all honest
_checks round number that all parties decide and monitor how many parties succeed by rounds run_
-- in round limits `r` in [5,10,15,20,25]
-- parties from 10 to 15
-- run __(3) benOrEnvAllHonestShuffle__
* assert (number of ouputs at most 1)
* collect (r, number of parties that output) 
### propBenOrSafetyAllHonest{CCC,...,SSS}

(3) propBenOrSucceedSim
-----------------------
_checks whether simulator holds for ALL HONEST_
-- 10 parties
-- run __(3) propBenOrAllHonestShuffle__
-- assert (tIdeal == tReal)

(4) propBenOrFindThreshold
--------------------------
_goal is to determine how many parties need to propose a value after which it's not possible to decide the opposite_
-- 10 parties, no corruptions
-- over numT in [5,6,7,8]
    * run __(3)/(4) benOrEnvAllHonestTestOutcome/benOrEnvAllHonestShuffle__
    * pre (at least someone decided)
    * assert (safety)
    * monitor (numT, numF, decision)

(5) propBenOrObserve
--------------------
-- parties = [ Alice, ..., Frank ]
-- crupt = [ Alice ]
-- run __(1) benOrEnvRandomRounds__
-- pre (all honest decide)
-- collect (round where last party decided)
