{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}

module MapPlugin ( plugin ) where

-- base
import Control.Arrow
  ( second )
import Control.Monad
  ( join )
import Data.Either
  ( partitionEithers )
import Data.Maybe
  ( catMaybes )

-- ghc
import qualified GHC
    ( Module, ModuleName
    , mkModuleName
    )
import qualified GHC.Driver.Finder
  as GHC
    ( FindResult(..) )
import qualified GHC.Data.FastString
  as GHC
    ( FastString, fsLit )
import qualified GHC.Plugins
  as GHC
    ( Plugin(..), defaultPlugin, purePlugin )
import qualified GHC.Core.DataCon
  as GHC
    ( DataCon )
import qualified GHC.Core.TyCon
  as GHC
    ( TyCon(..) )
import qualified GHC.Tc.Plugin
  as GHC
    ( findImportedModule
    , lookupOrig, tcLookupTyCon, tcLookupDataCon
    )
import qualified GHC.Tc.Types
  as GHC
    ( TcPlugin(..)
    , TcPluginM
    , TcPluginResult(..)
    )
import qualified GHC.Tc.Types.Constraint
  as GHC
    ( Ct(..) )
import qualified GHC.Tc.Types.Evidence
  as GHC
    ( EvTerm )
import qualified GHC.Types.Name.Occurrence
  as GHC
    ( mkDataOcc, mkTcOcc )
import qualified GHC.Utils.Outputable
  as GHC
    ( ppr, pprTrace )

--------------------------------------------------------------------------------

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.tcPlugin        = tcPlugin
    , GHC.pluginRecompile = GHC.purePlugin
    }

tcPlugin :: [ String ] -> Maybe GHC.TcPlugin
tcPlugin _args =
  Just $
    GHC.TcPlugin
      { GHC.tcPluginInit  = tcPluginInit
      , GHC.tcPluginSolve = tcPluginSolve
      , GHC.tcPluginStop  = tcPluginStop
      }

data PluginDefs =
  PluginDefs
    { keyValTyCon     :: !GHC.TyCon
    , keyValDataCon   :: !GHC.DataCon
    , mapTyCon        :: !GHC.TyCon
    , fromListDataCon :: !GHC.DataCon
    , lookupTyCon     :: !GHC.TyCon
    , deleteTyCon     :: !GHC.TyCon
    , unionTyCon      :: !GHC.TyCon
    , differenceTyCon :: !GHC.TyCon
    }

tcPluginInit :: GHC.TcPluginM PluginDefs
tcPluginInit = withDataTypeMapModule \ dataTypeMapModule -> do
  keyValTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   ":->"        )
  keyValDataCon   <- GHC.tcLookupDataCon =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkDataOcc ":->"        )
  mapTyCon        <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Map"        )
  fromListDataCon <- GHC.tcLookupDataCon =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkDataOcc "FromList"   )
  lookupTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Lookup"     )
  deleteTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Delete"     )
  unionTyCon      <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Union"      )
  differenceTyCon <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Difference" )
  pure ( PluginDefs { .. } )

withDataTypeMapModule :: ( GHC.Module -> GHC.TcPluginM a ) -> GHC.TcPluginM a
withDataTypeMapModule f = do
  findResult <- GHC.findImportedModule modName mbPkg
  case findResult of
    GHC.Found _ res     -> f res
    GHC.FoundMultiple _ -> error "MapPlugin: found multiple modules named \"Data.Type.Map\"."
    _                   -> error "MapPlugin: could not find any module named \"Data.Type.Map\"."
  where
    modName :: GHC.ModuleName
    modName = GHC.mkModuleName "Data.Type.Map"
    mbPkg :: Maybe GHC.FastString
    mbPkg = Just ( GHC.fsLit "Map-Plugin" )

tcPluginStop :: PluginDefs -> GHC.TcPluginM ()
tcPluginStop _ = pure ()

tcPluginSolve :: PluginDefs -> [ GHC.Ct ] -> [ GHC.Ct ] -> [ GHC.Ct ] -> GHC.TcPluginM GHC.TcPluginResult
tcPluginSolve _state _givens _deriveds []      = pure $ GHC.TcPluginOk [] []
tcPluginSolve  state  givens  deriveds wanteds = do
  ( contras, oks )
    <- partitionEithers
    .  catMaybes
    <$> traverse ( \ wanted -> specifyWanted wanted <$> solveWanted state givens deriveds wanted ) wanteds
  case contras of
    [] ->
      let
        solveds :: [ ( GHC.EvTerm, GHC.Ct ) ]
        news    :: [ GHC.Ct ]
        ( solveds, news ) = second join ( unzip oks )
      in  pure $ GHC.TcPluginOk solveds news
    _  -> pure $ GHC.TcPluginContradiction contras

data SolverResult
  = Ignore
  | Solved
    { evidence   :: !GHC.EvTerm
    , newWanteds :: ![ GHC.Ct ]
    }
  | Contradiction

specifyWanted :: GHC.Ct -> SolverResult -> Maybe ( Either GHC.Ct ( ( GHC.EvTerm, GHC.Ct ), [ GHC.Ct ] ) )
specifyWanted _      Ignore            = Nothing
specifyWanted wanted ( Solved { .. } ) = Just ( Right ( ( evidence, wanted ), newWanteds ) )
specifyWanted wanted Contradiction     = Just ( Left wanted )

solveWanted :: PluginDefs -> [ GHC.Ct ] -> [ GHC.Ct ] -> GHC.Ct -> GHC.TcPluginM SolverResult
solveWanted ( PluginDefs {} ) _givens _derived wanted = GHC.pprTrace "" ( GHC.ppr wanted ) $ pure Ignore
