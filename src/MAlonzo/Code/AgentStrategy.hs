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

module MAlonzo.Code.AgentStrategy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agent
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Institution
import qualified MAlonzo.Code.PriceGrid
import qualified MAlonzo.Code.Proposal

-- AgentStrategy.CertifiedBid
d_CertifiedBid_4 a0 = ()
data T_CertifiedBid_4
  = C_constructor_16 MAlonzo.Code.Proposal.T_Proposal_2
                     MAlonzo.Code.Institution.T_BuyerAdmissible_6
-- AgentStrategy.CertifiedBid.proposal
d_proposal_12 ::
  T_CertifiedBid_4 -> MAlonzo.Code.Proposal.T_Proposal_2
d_proposal_12 v0
  = case coe v0 of
      C_constructor_16 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- AgentStrategy.CertifiedBid.admissible
d_admissible_14 ::
  T_CertifiedBid_4 -> MAlonzo.Code.Institution.T_BuyerAdmissible_6
d_admissible_14 v0
  = case coe v0 of
      C_constructor_16 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- AgentStrategy.CertifiedAsk
d_CertifiedAsk_20 a0 = ()
data T_CertifiedAsk_20
  = C_constructor_32 MAlonzo.Code.Proposal.T_Proposal_2
                     MAlonzo.Code.Institution.T_SellerAdmissible_26
-- AgentStrategy.CertifiedAsk.proposal
d_proposal_28 ::
  T_CertifiedAsk_20 -> MAlonzo.Code.Proposal.T_Proposal_2
d_proposal_28 v0
  = case coe v0 of
      C_constructor_32 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- AgentStrategy.CertifiedAsk.admissible
d_admissible_30 ::
  T_CertifiedAsk_20 -> MAlonzo.Code.Institution.T_SellerAdmissible_26
d_admissible_30 v0
  = case coe v0 of
      C_constructor_32 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- AgentStrategy.makeBuyerBid
d_makeBuyerBid_38 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 -> T_CertifiedBid_4
d_makeBuyerBid_38 v0 v1 v2 ~v3 = du_makeBuyerBid_38 v0 v1 v2
du_makeBuyerBid_38 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_CertifiedBid_4
du_makeBuyerBid_38 v0 v1 v2
  = coe
      C_constructor_16
      (coe
         MAlonzo.Code.Proposal.C_constructor_16
         (coe MAlonzo.Code.Agent.d_id_30 (coe v1))
         (coe du_p_56 (coe v0) (coe v1) (coe v2))
         (coe MAlonzo.Code.Agent.C_Buyer_4))
      (coe
         MAlonzo.Code.Institution.C_constructor_20
         (coe
            MAlonzo.Code.PriceGrid.du_buyerTickBelowValuation_148 (coe v0)
            (coe du_v_52 (coe v1)) (coe du_b_54 (coe v1)) (coe v2))
         (coe
            MAlonzo.Code.PriceGrid.du_buyerTickWithinBudget_168 (coe v0)
            (coe du_v_52 (coe v1)) (coe du_b_54 (coe v1)) (coe v2)))
-- AgentStrategy._.v
d_v_52 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_v_52 ~v0 v1 ~v2 ~v3 = du_v_52 v1
du_v_52 ::
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_v_52 v0
  = coe
      MAlonzo.Code.Agent.d_unitValue_12
      (coe MAlonzo.Code.Agent.d_valuation_34 (coe v0))
-- AgentStrategy._.b
d_b_54 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_b_54 ~v0 v1 ~v2 ~v3 = du_b_54 v1
du_b_54 ::
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_b_54 v0 = coe MAlonzo.Code.Agent.d_budget_36 (coe v0)
-- AgentStrategy._.p
d_p_56 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_p_56 v0 v1 v2 ~v3 = du_p_56 v0 v1 v2
du_p_56 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_p_56 v0 v1 v2
  = coe
      MAlonzo.Code.PriceGrid.d_buyerTick_130 (coe v0)
      (coe du_v_52 (coe v1)) (coe du_b_54 (coe v1)) (coe v2)
-- AgentStrategy.makeSellerAsk
d_makeSellerAsk_64 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_CertifiedAsk_20
d_makeSellerAsk_64 v0 v1 v2 v3 ~v4 v5
  = du_makeSellerAsk_64 v0 v1 v2 v3 v5
du_makeSellerAsk_64 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_CertifiedAsk_20
du_makeSellerAsk_64 v0 v1 v2 v3 v4
  = coe
      C_constructor_32
      (coe
         MAlonzo.Code.Proposal.C_constructor_16
         (coe MAlonzo.Code.Agent.d_id_30 (coe v1))
         (coe du_p_84 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe MAlonzo.Code.Agent.C_Seller_6))
      (coe
         MAlonzo.Code.Institution.C_constructor_40
         (coe
            MAlonzo.Code.PriceGrid.du_sellerTickAboveValuation_214 (coe v0)
            (coe du_v_82 (coe v1)) (coe v2) (coe v3))
         (coe v4))
-- AgentStrategy._.v
d_v_82 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_v_82 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_v_82 v1
du_v_82 ::
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_v_82 v0
  = coe
      MAlonzo.Code.Agent.d_unitValue_12
      (coe MAlonzo.Code.Agent.d_valuation_34 (coe v0))
-- AgentStrategy._.p
d_p_84 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_p_84 v0 v1 v2 v3 ~v4 ~v5 = du_p_84 v0 v1 v2 v3
du_p_84 ::
  Integer ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_p_84 v0 v1 v2 v3
  = coe
      MAlonzo.Code.PriceGrid.d_sellerTick_182 (coe v0)
      (coe du_v_82 (coe v1)) (coe v2) (coe v3)
