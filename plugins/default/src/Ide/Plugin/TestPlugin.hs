{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}

#include "ghc-api-version.h"

module Ide.Plugin.TestPlugin (descriptor) where

import           Control.DeepSeq
import           Control.Monad.IO.Class
import           Data.Aeson                           (ToJSON (toJSON),
                                                       Value (Null))
import           Data.Aeson.Types                     (FromJSON)
import qualified Data.HashMap.Strict                  as HashMap
import           Data.IORef                           (readIORef)
import qualified Data.Map.Strict                      as Map
import           Data.Maybe                           (catMaybes, fromMaybe, fromJust)
import qualified Data.Text                            as T                   
import           Development.IDE
import           Development.IDE.Core.PositionMapping
import           Development.IDE.GHC.Compat
import           Development.Shake.Classes
import           GHC.Generics                         (Generic)
import           Ide.PluginUtils                      (mkLspCommand)
import           Ide.Types
import           Language.LSP.Server
import           Language.LSP.Types
import           TcRnMonad                            (initTcWithGbl)
import           TcRnTypes                            (TcGblEnv (tcg_used_gres))

-- ---------------------------------------------------------------------

lhsCommandId :: CommandId
lhsCommandId = "lhsGeneratorCommand"

descriptor :: PluginId -> PluginDescriptor IdeState
descriptor plId =
  (defaultPluginDescriptor plId)
    {
      pluginCommands = [lhsCommand],
      pluginRules = getSigsRule,
      pluginHandlers = mconcat
        [ 
          mkPluginHandler STextDocumentCodeLens lensProvider
        ]
    }

lhsCommand :: PluginCommand IdeState
lhsCommand =
  PluginCommand lhsCommandId "LHS generator command" runLHSCommand

data LhsCommandParams = LhsCommandParams WorkspaceEdit
  deriving (Generic)
  deriving anyclass (FromJSON, ToJSON)

runLHSCommand :: CommandFunction IdeState LhsCommandParams
runLHSCommand _state (LhsCommandParams edit) = do
  _ <- sendRequest SWorkspaceApplyEdit (ApplyWorkspaceEditParams Nothing edit) (\_ -> pure ())
  return (Right Null)


lensProvider :: PluginMethodHandler IdeState TextDocumentCodeLens
lensProvider
  state 
  pId 
  CodeLensParams {_textDocument = TextDocumentIdentifier {_uri}}
    | Just nfp <- uriToNormalizedFilePath $ toNormalizedUri _uri = liftIO $
      do
        mbSigs <- runAction "" state $ useWithStale Sigs nfp 
        case mbSigs of
          Just (SigsResult sigs, posMapping) -> do
            commands <-
              sequence
                [ generateLens pId _uri edit
                  | (decl, Just signature) <- sigs,
                    Just edit <- [mkExplicitEdit posMapping decl signature]
                ]
            return $ Right (List $ catMaybes commands)
          _ ->
            return $ Right (List [])
    | otherwise =
      return $ Right (List [])




--------------------------------------------------------------------------------

data Sigs= Sigs
  deriving (Show, Generic, Eq, Ord)

instance Hashable Sigs

instance NFData Sigs

instance Binary Sigs

type instance RuleResult Sigs = SigsResult

newtype SigsResult = SigsResult
  {getSigsResult :: [(LHsDecl GhcPs, Maybe T.Text)]}

instance Show SigsResult where show _ = "<getSignaturesResult>"

instance NFData SigsResult where rnf = rwhnf

getSigsRule :: Rules ()
getSigsRule = define $ \Sigs nfp -> do
  tmr <- use TypeCheck nfp
  hsc <- use GhcSessionDeps nfp
  mbSigs <- liftIO $ extractSignatures hsc tmr
  let sigsMap =
        Map.fromList
          [ (srcSpanStart l, T.pack (prettyPrint i))
            | L l i <- fromMaybe [] mbSigs
          ]
      res =
        [ (s, Map.lookup (srcSpanStart (getLoc s)) sigsMap)
          | s <- fromMaybe [] mbSigs
        ]
  return ([], SigsResult res <$ mbSigs)

--------------------------------------------------------------------------------

extractSignatures ::
  Maybe HscEnvEq ->
  Maybe TcModuleResult ->
  IO (Maybe [LHsDecl GhcPs])
extractSignatures (Just hsc) (Just TcModuleResult {..}) = do
  let ParsedModule {pm_parsed_source = L loc mod} = tmrParsed

  let decls = getDecls mod
      sigs = filter isSig decls

  if null sigs then return Nothing else return $ Just sigs
extractSignatures _ _ = return Nothing

getDecls :: HsModule GhcPs -> [LHsDecl GhcPs]
getDecls HsModule {..} = hsmodDecls

isSig :: LHsDecl GhcPs -> Bool
isSig (L l (SigD _ _)) = True
isSig _ = False  

mkExplicitEdit :: PositionMapping -> LHsDecl pass -> T.Text -> Maybe TextEdit
mkExplicitEdit posMapping (L src sig) explicit
  | RealSrcSpan l <- src,
    Just rng <- toCurrentRange posMapping $ realSrcSpanToRange l =
      Just $ TextEdit (incRng rng) $ mkFunc
        $ T.unwords $ firsts $ init $ split  
  | otherwise = Nothing
      where space = T.pack " "
            arrow = T.pack "->"
            colons = T.pack "::"
            empty = T.pack ""
            pred = T.pack "=>"
            eqHole = T.pack " = _"
            split = (\(x, y) -> (T.strip x) : (T.splitOn arrow $ remPred $
                        fromJust $ T.stripPrefix colons y)) $ T.breakOn colons explicit 
            mkFunc t = T.append t (eqHole)
            remPred t = (\(x, y) -> fromMaybe x $ T.stripPrefix pred y) $ T.breakOn pred t
            firsts (x:xs) = x : (uniquify $ map lowerFirst $ abbrev $ map T.strip xs)
            firsts [] = []
            abbrev (t:ts) = (T.concat $ checkList $ T.words t) : (abbrev ts)
            abbrev [] = []
            checkList (t:ts) = if T.head t == '[' 
                          then  (checkParens $ T.drop 1 t)  : (checkList ts ++ [T.singleton 's'])
                          else (checkParens t) : checkList ts
            checkList [] = []
            checkParens t
              |isTuple t = T.pack "sjadi"
              |T.head t == '(' = (T.singleton $ T.head $ T.drop 1 t)
              |otherwise = (T.singleton $ T.head t)
            isTuple t = False
            lowerFirst t = T.append (T.toLower $ T.singleton $ T.head t) (T.tail t)
            uniquify (x:xs) = (T.snoc x '1') : (uniquify' xs (Map.singleton x 1))
            uniquify [] = []
            uniquify' (x:xs) map = 
              (\newmap -> T.append x (T.pack $ show $ fromJust $ Map.lookup x newmap) 
                  : (uniquify' xs newmap))
              (Map.insertWith (\x y -> y + 1) x 1 map)
            uniquify' [] _ = []
            incRng (Range (Position l1 c1) (Position l2 c2)) = 
                Range (Position (l2 + 1) c1) (Position (l2 + 1) c2)


-- | Given an import declaration, generate a code lens unless it has an
-- explicit import list or it's qualified
generateLens :: PluginId -> Uri -> TextEdit -> IO (Maybe CodeLens)
generateLens pId uri importEdit@TextEdit {_range} = do
  -- The title of the command is just the minimal explicit import decl
  let title = _newText importEdit
      -- the code lens has no extra data
      _xdata = Nothing
      -- an edit that replaces the whole declaration with the explicit one
      edit = WorkspaceEdit (Just editsMap) Nothing
      editsMap = HashMap.fromList [(uri, List [importEdit])]
      -- the command argument is simply the edit
      _arguments = Just [toJSON $ LhsCommandParams edit]
  -- create the command
      _command = Just $ mkLspCommand pId lhsCommandId title _arguments
  -- create and return the code lens
  return $ Just CodeLens {..}

-- | A helper to run ide actions
runIde :: IdeState -> Action a -> IO a
runIde state = runAction "importLens" state

--------------------------------------------------------------------------------

within :: Range -> SrcSpan -> Bool
within (Range start end) span =
  isInsideSrcSpan start span || isInsideSrcSpan end span

