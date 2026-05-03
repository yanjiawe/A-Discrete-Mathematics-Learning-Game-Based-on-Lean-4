import GameServer.Commands
import Game.Levels.FirstWorld
import Game.Levels.secondworld
import Game.Levels.ThirdWorld
import Game.Levels.ForthWorld
import Game.Levels.FifthWorld
import Game.Levels.sixthworld
-- Here's what we'll put on the title screen


--Dependency Firstworld→Secondworld
--Dependency Secondworld→thirdworld
--Dependency thirdworld→forthworld
--Dependency forthworld→fifthworld


Title "一个基于Lean 4的离散数学游戏"
Introduction
"
欢迎来到离散数学游戏的世界，在本世界你将通过对不同世界的闯关逐渐习得离散数学
相关的知识，大致范围涵盖了命题，一阶逻辑，集合论，代数结构，图论等部分的重要
定理。本世界使用Lean4实现，在形式化证明的过程中你将加强对Lean的掌握并且加深
对离散数学知识的掌握。
本世界分为三种模式，分别是闯关模式，全关卡模式，全关卡全策略模式，你可以自由
挑选游玩。
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use **markdown**.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
