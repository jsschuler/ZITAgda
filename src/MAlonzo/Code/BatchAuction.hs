{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.BatchAuction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.AgentStrategy
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Properties
import qualified MAlonzo.Code.Institution
import qualified MAlonzo.Code.Proposal
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- BatchAuction.BidEntry
d_BidEntry_2 :: ()
d_BidEntry_2 = erased
-- BatchAuction.AskEntry
d_AskEntry_4 :: ()
d_AskEntry_4 = erased
-- BatchAuction.tryMatch
d_tryMatch_6 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Institution.T_Match_42
d_tryMatch_6 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            (coe MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60)
                            (coe
                               MAlonzo.Code.Data.Rational.Properties.du_drop'45''42''8804''42'_3534)
                            (coe
                               MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880
                               (coe
                                  MAlonzo.Code.Data.Integer.Base.d__'42'__316
                                  (coe
                                     MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                     (coe
                                        MAlonzo.Code.Proposal.d_price_12
                                        (coe MAlonzo.Code.AgentStrategy.d_proposal_28 (coe v5))))
                                  (coe
                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                     (coe
                                        MAlonzo.Code.Proposal.d_price_12
                                        (coe MAlonzo.Code.AgentStrategy.d_proposal_12 (coe v3)))))
                               (coe
                                  MAlonzo.Code.Data.Integer.Base.d__'42'__316
                                  (coe
                                     MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                     (coe
                                        MAlonzo.Code.Proposal.d_price_12
                                        (coe MAlonzo.Code.AgentStrategy.d_proposal_12 (coe v3))))
                                  (coe
                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                     (coe
                                        MAlonzo.Code.Proposal.d_price_12
                                        (coe
                                           MAlonzo.Code.AgentStrategy.d_proposal_28 (coe v5)))))) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then case coe v8 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Institution.C_constructor_80 (coe v2)
                                               (coe v4)
                                               (coe
                                                  MAlonzo.Code.AgentStrategy.d_proposal_12 (coe v3))
                                               (coe
                                                  MAlonzo.Code.AgentStrategy.d_proposal_28 (coe v5))
                                               (coe
                                                  MAlonzo.Code.AgentStrategy.d_admissible_14
                                                  (coe v3))
                                               (coe
                                                  MAlonzo.Code.AgentStrategy.d_admissible_30
                                                  (coe v5))
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Proposal.d_price_12
                                                  (coe
                                                     MAlonzo.Code.AgentStrategy.d_proposal_28
                                                     (coe v5)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Properties.d_'8804''45'refl_3606
                                                     (coe
                                                        MAlonzo.Code.Proposal.d_price_12
                                                        (coe
                                                           MAlonzo.Code.AgentStrategy.d_proposal_28
                                                           (coe v5))))
                                                  (coe v9)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v8) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- BatchAuction.collectMatches
d_collectMatches_40 ::
  () ->
  (AgdaAny -> Maybe MAlonzo.Code.Institution.T_Match_42) ->
  [AgdaAny] -> [MAlonzo.Code.Institution.T_Match_42]
d_collectMatches_40 ~v0 v1 v2 = du_collectMatches_40 v1 v2
du_collectMatches_40 ::
  (AgdaAny -> Maybe MAlonzo.Code.Institution.T_Match_42) ->
  [AgdaAny] -> [MAlonzo.Code.Institution.T_Match_42]
du_collectMatches_40 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4 = coe v0 v2 in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                       (coe du_collectMatches_40 (coe v0) (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe du_collectMatches_40 (coe v0) (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- BatchAuction.matchPairs
d_matchPairs_68 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Institution.T_Match_42]
d_matchPairs_68 v0 v1
  = case coe v0 of
      [] -> coe v0
      (:) v2 v3
        -> case coe v1 of
             [] -> coe v1
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe du_collectMatches_40 (coe d_tryMatch_6 (coe v2)) (coe v1))
                    (coe
                       d_matchPairs_68 (coe v3)
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- BatchAuction.matchZip
d_matchZip_78 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Institution.T_Match_42]
d_matchZip_78 v0 v1
  = case coe v0 of
      [] -> coe v0
      (:) v2 v3
        -> case coe v1 of
             [] -> coe v1
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       du_collectMatches_40 (coe d_tryMatch_6 (coe v2))
                       (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v4)))
                    (coe d_matchZip_78 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
