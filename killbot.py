#!/usr/bin/env python
#
# Copyright 2011. All Rights Reserved.

"""Kill bot."""

__author__ = 'schrepfer'

import datetime
import fnmatch
import logging
import math
import optparse
import os
import pickle
import pprint
import random
import re
import sys
import time

sys.path.insert(0, os.path.dirname(__file__) + '/pybot.zip')

from pybot import bot
from pybot import config
from pybot import events


WIZARDS = [
    'altair', 'anna', 'arakorni', 'arthedain', 'avandhar', 'azynya', 'balin',
    'belabour', 'break', 'brennan', 'cheule', 'core', 'daln', 'darc', 'darku',
    'del', 'deneb', 'deolon', 'deron', 'dranil', 'dusk', 'duval', 'endy', 'eod',
    'euna', 'explicit', 'farthon', 'fast', 'finderne', 'fizzban', 'fluffy',
    'friegaah', 'gandhi', 'gargo', 'geldan', 'geldor', 'gevalia', 'gonth',
    'goretongue', 'gorka', 'graerth', 'gregor', 'grungemen', 'hair', 'hammanu',
    'hub', 'hubo', 'jaden', 'jagmis', 'jared', 'juiblex', 'juicer', 'kaahn',
    'kaarle', 'kabul', 'katiria', 'kingsman', 'kreator', 'kroisos', 'larssi',
    'leper', 'lepwiztest', 'limit', 'lix', 'looser', 'loyd', 'macic', 'malys',
    'manowar', 'mehtar', 'mela', 'melkpak', 'miukkali', 'mobius', 'monte',
    'moongleam', 'morgil', 'mvx', 'neckbreaker', 'nek', 'noose', 'nullnull',
    'odium', 'om', 'opola', 'osir', 'pancreas', 'phileas', 'pim', 'pittis',
    'qase', 'salainen', 'selth', 'sepe', 'seth', 'sihu', 'squizzy', 'status',
    'sumppen', 'superfro', 'terorist', 'troops', 'turnipsi', 'ulme', 'viktor',
    'waaar', 'wilde', 'yaga', 'zagarus', 'zantar', 'zebo', 'zeith',
    ]

GAGS = {
  'simple': [
      'Get what?',
      ],
  'glob': [
      'p: *',
      ],
  'regexp': [
      ],
  }

MIN_RESET = 15*60


class TimeZone(datetime.tzinfo):
  """Eastern European Time."""

  def __init__(self, name, offset):
    self._name = name
    self._offset = offset

  def utcoffset(self, unused_dt):
    return datetime.timedelta(hours=self._offset)

  def dst(self, unused_dt):
    return datetime.timedelta(hours=self._offset - 1)

  def tzname(self, unused_dt):
    return self._name


EET = TimeZone('Europe/Helsinki', 3)


class Npc(object):

  def __init__(self, **kwargs):
    self._id = kwargs.get('id')
    self._size = kwargs.get('size', 0)
    self._moves = kwargs.get('moves', False)

  @property
  def id(self):
    return self._id

  @property
  def size(self):
    return self._size

  @property
  def moves(self):
    return self._moves

  def isValid(self, min_size, max_size):
    return not self.size or (self.size >= min_size and self.size <= max_size)

class Area(object):

  def __init__(self, **kwargs):
    self._name = kwargs.get('name')
    self._outside = kwargs.get('outside', False)
    self._paths = kwargs.get('paths', [])
    self._npcs = dict(
        (x, Npc(**y)) for x, y in kwargs.get('npcs', {}).iteritems())

  @property
  def name(self):
    return self._name

  @property
  def outside(self):
    return self._outside

  @property
  def paths(self):
    return self._paths

  @property
  def npcs(self):
    return self._npcs

  def hasValidNpcs(self, min_size, max_size):
    for n in self._npcs.values():
      if n.isValid(min_size, max_size):
        return True
    return False


def loadArea(area):
  basename = 'areas.%s' % area
  try:
    module = reload(__import__(basename))
  except ImportError, e:
    print('ImportError: %s' % e)
    return None
  except NameError, e:
    print('NameError: %s' % e)
    return None
  except SyntaxError, e:
    print('Syntax error on line %d: %s' % (e.lineno, e.filename))
    return None

  area_module = getattr(module, area)
  area_dict = getattr(area_module, 'AREA', {})
  return Area(name=area, **area_dict)


def loadAreas(areas):
  root = os.path.dirname(sys.argv[0])
  result = []
  if areas:
    for area in areas:
      result.append(loadArea(area))
  return result


def reloadAreas(areas):
  return loadAreas(x.name for x in areas if x and x.name)


def running(function):
  def wrapper(self, *args, **kwargs):
    if not self._running:
      return True
    function(self, *args, **kwargs)
  return wrapper


def action(*actions):
  def decorator(function):
    def wrapper(self, *args, **kwargs):
      if self._action not in actions:
        return True
      function(self, *args, **kwargs)
    return wrapper
  return decorator


class KillBot(bot.Bot):

  RESET = 'RESET'
  MOVING = 'MOVING'
  KILLING = 'KILLING'
  SEARCHING = 'SEARCHING'
  SCANNING = 'SCANNING'
  OTHER = 'OTHER'
  SPENDING = 'SPENDING'
  TICKING = 'TICKING'
  HEALING = 'HEALING'
  KAMIKAZE = 'KAMIKAZE'
  STUNNED = 'STUNNED'
  RESET_SLEEP = 'RESET_SLEEP'

  def __init__(self, options, trains=None, areas=None):
    self._running = True
    self._file_handle = None
    self._last_send = 0
    self._last_reset = 0
    self._options = options
    self._prompt = {}
    self._score = {}
    self._queue = []
    self._players = False
    self._chain = 0
    self._chain_last = 0
    self._iterator = None
    self._area = None
    self._areas = loadAreas(areas)
    self._action = self.RESET
    self._last_action = self.RESET
    self._target = None
    self._target_name = None
    self._trains = trains
    self._stunned = False
    self._whats = []
    self._foreign_attackers = []
    self._talked = set()
    super(KillBot, self).__init__()

  @property
  def night(self):
    now = datetime.datetime.now(EET)
    minute = now.hour * 60 + now.minute
    return minute > 30 and minute < 420

  @property
  def options(self):
    return self._options

  @property
  def queue(self):
    return self._queue

  def status(self, message, *args):
    print '\x1b[36m%% %s\x1b[0m' % (message % args)

  def error(self, message, *args):
    print '\x1b[31m%% %s\x1b[0m' % (message % args)

  def isGagged(self, line):
    if line in GAGS['simple']:
      return True
    for pattern in GAGS['glob']:
      if fnmatch.fnmatch(line, pattern):
        return True
    for pattern in GAGS['regexp']:
      if re.search(pattern, line):
        return True
    return False

  @events.event(events.READ)
  def onRead(self, line):
    stripped = bot.ANSI_COLOR_PATTERN.sub('', line)
    if self.options.display and not self.isGagged(stripped):
      #sys.stdout.write('[%s] %s\n' % (time.strftime('%H:%M:%S'), line))
      sys.stdout.write('%s\n' % line)
    if self._file_handle:
      self._file_handle.write(stripped + '\n')
      #self._file_handle.write(line + '\n')
      self._file_handle.flush()
    return super(KillBot, self).onRead(line)

  def send(self, commands, splitlines=True, escape=True):
    if splitlines:
      commands = commands.split(';')
    else:
      commands = [commands]
    for command in commands:
      if not command:
        continue
      self.engine.eventManager.triggerEvent(
          events.SEND, ('!' if escape else '') + command)

  @events.event(events.SEND)
  def onSend(self, line):
    if self._file_handle:
      self._file_handle.write('# '  + line + '\n')
      self._file_handle.flush()
    self._last_send = time.time()
    return True

  @property
  def idle(self):
    return time.time() - self._last_send

  def executeCommand(self, line):
    if ' ' in line:
      command, args = line.split(' ', 1)
    else:
      command, args = line, []
    if command == 'z':
      self.send(args)
      return
    if command == 'prompt':
      for key, value in sorted(self._prompt.iteritems()):
        self.status('%12s: %s' % (key, value))
      return
    if command == 'start':
      self.startBot()
      return
    if command == 'resume':
      self.resumeBot()
      return
    if command == 'reload':
      self.reloadAreas()
      return
    if command == 'next':
      self.chain(self.MOVING, 'MANUAL OVERRIDE')
      return
    if command == 'stop':
      self.stopBot()
      return
    if command == 'trigger':
      self.engine.eventManager.triggerEvent(events.READ, args)
      return
    if command in ('expr', 'eval'):
      self.status('%s\n%s' % (args, pprint.pformat(eval(args))))
      return
    if command in ('now', 'time'):
      self.status('%s', datetime.datetime.now(EET))
      return
    if command == 'chain':
      try:
        self.chain(args, 'MANUAL OVERRIDE')
      except:
        pass
      return
    if command == 'spend':
      self.spend()
      return
    if command == 'sell':
      self.sell()
      return
    if command in ('da', 'deposit'):
      self.deposit()
      return
    self.error('Unknown command: %s' % command)

  @events.event(events.INPUT)
  def onInput(self, line):
    if line.startswith('/'):
      self.executeCommand(line.lstrip('/'))
      return
    self.engine.eventManager.triggerEvent(events.SEND, line)

  @events.event(events.STARTUP)
  def onStartup(self):
    if self._file_handle:
      self._file_handle.close()
    self._file_handle = open(self.options.log, 'w')
    self.connection.connect(self.options.address, self.options.port)
    return True

  @events.event(events.SHUTDOWN)
  def onShutdown(self):
    if self._file_handle:
      self._file_handle.close()
    return True

  def clearPrompt(self):
    self.send('prompt <plain>')

  def setPrompt(self):
    self.send(
        'prompt p: <hp> <maxhp> <sp> <maxsp> <exp> <cash> <expl> <wgt> <last_exp> '
        '"<scan>" "<align>" <party><newline>')

  @events.event(events.CONNECT)
  def onConnect(self):
    self.send(self.options.username, escape=False)
    self.send(self.options.password, escape=False)
    return True

  @events.event(events.DISCONNECT)
  def onDisconnect(self):
    self.engine.startTimer(
      'reconnect', 5.0, self.connection.connect, self.options.address,
      self.options.port)
    return True

  def nightCheck(self):
    if self._running:
      if self.night or not self.options.nocturnal:
        if not self.connection.running():
          self.connection.connect(self.options.address, self.options.port)
      else:
        if self.connection.running():
          self.chain(self.RESET, 'NIGHT', force=True)
    self.engine.startTimer('nightCheck', 60.0, self.nightCheck)

  ALIGN = {
      'satanic': -6,
      'demonic': -5,
      'extremily evil': -4,
      'very evil': -3,
      'evil': -2,
      'slightly evil': -1,
      'neutral': 0,
      'slightly good': 1,
      'good': 1,
      'very good': 2,
      'extremly good': 3,
      'angelic': 4,
      'godly': 5,
      }

  def getAlign(self):
    align = self._prompt.get('align', '')
    return self.ALIGN.get(align.lower(), 0)

  @bot.trigger(r'^p: (-?\d+) (-?\d+) (-?\d+) (-?\d+) (-?\d+) (-?\d+) (-?\d+) (-?\d+) (-?\d+) "([^"]*)" "([^"]*)" (.*)$')
  def prompt(self, match):
    prompt = {
        'hp': int(match[1]),
        'maxhp': int(match[2]),
        'sp': int(match[3]),
        'maxsp': int(match[4]),
        'exp': int(match[5]),
        'cash': int(match[6]),
        'expl': int(match[7]),
        'wgt': int(match[8]),
        'last_exp': int(match[9]),
        'scan': match[10],
        'align': match[11],
        'party': match[12],
        }

    # Some action?

    self._prompt = prompt

  @bot.trigger(r'^hp: (-?\d+)\((\d+)\) sp: (-?\d+)\((\d+)\)$')
  def shortScore(self, match):
    score = {
        'hp': int(match[1]),
        'maxhp': int(match[2]),
        'sp': int(match[3]),
        'maxsp': int(match[4]),
        }

    hp_diff = score['hp'] - self._score.get('hp', 0)
    sp_diff = score['sp'] - self._score.get('sp', 0)

    self._score = score
    self._prompt.update(score)

    if not self._running:
      return

    if self._action == self.TICKING and (hp_diff > 0 or sp_diff > 0):
      self.chain(self.OTHER, 'TICKED')
      return

    if self._action == self.KILLING:
      if hp_diff < 0 and score['hp'] < score['maxhp'] * 0.50:
        self.chain(self.MOVING, 'WIMPY')
        return

      if  hp_diff < score['maxhp'] * -0.10:
        self.chain(self.MOVING, 'DAMAGE 10%')
        return

  def reloadAreas(self):
    self._areas = reloadAreas(self._areas)

  def startBot(self):
    self._running = True
    self._iterator = self.loop()
    self.chain(self.MOVING, 'STARTING')

  def stopBot(self):
    self._running = False
    self.engine.killTimer('chain')

  def resumeBot(self):
    if self._iterator is None:
      return self.startBot()
    self._running = True
    self.chain(self.MOVING, 'RESUMING')

  def sell(self):
    self.send(
        '3 n;e;s;sell noeq;'
        'n;w;2 s;e;sell noeq;'
        '2 w;sell noeq;'
        'e;s')

  def spend(self):
    self.withdraw(0.00045 * self._prompt['exp'] - self._prompt['cash'])
    self.send(
        '3 n;2 w;s;advance;se;request;'
        'nw;n;w;transport ' + self.options.guild + ';'
        'advance')

    for train in self._trains:
      self.send('train %s' % train)

    self.chain(self.RESET, 'DONE SPENDING')

  def deposit(self):
    self.send('2 n;w;deposit all;e;2 s')

  def withdraw(self, amount):
    if amount > 1:
      self.send('2 n;w;withdraw %d;e;2 s' % amount)

  @bot.trigger(r'^.inform.: ([A-Z][a-z]+) enters the game\.$')
  @running
  def entersGame(self, match):
    if match[1].lower() != self.options.username:
      return
    self._action = self.RESET
    self._last_reset = time.time()
    self.engine.startTimer(
        'tell', 1.0, self.send, 'tell %s .' % self.options.username,
        escape=False)

  @bot.trigger(r"^You tell ([A-Z][a-z]+) \(GHOST\) '\.'$")
  @running
  def ghostTell(self, match):
    if match[1].lower() != self.options.username:
      return
    self.stopBot()

  @bot.trigger(r"^You tell ([A-Z][a-z]+) '\.'$")
  @running
  def liveTell(self, match):
    if match[1].lower() != self.options.username:
      return
    self.setPrompt()
    self.send('wimpy 20')
    self.send('sc on')
    self.send('chain %s:%s' % (self.options.sksp, self.options.sksp))
    self.send('party create %s' % self.options.username[0].upper())
    self.send('equip')
    self.send('save')
    self.send('score')
    self.send('style_score')
    self.send('n;e')
    self.send('set nomore on')
    self.deposit()
    self._iterator = self.loop()
    self.engine.startTimer('chain', 2.0, self.chain, self.MOVING, 'STARTING')

  @bot.trigger(r'^.inform.: ([A-Z][a-z]+) recovers from link death\.$')
  @running
  def recoversLinkDeath(self, match):
    if match[1].lower() != self.options.username:
      return
    self.chain(self.RESET, 'LINK DEATH')

  @bot.trigger('You can not quit while fighting.', matcher=bot.SimpleMatcher)
  @running
  @action(RESET)
  def canNotQuit(self, match):
    self.engine.startTimer(
        'reset', 1.0, self.chain, self._action, 'FAILED QUIT', force=True)

  @bot.trigger(r'^(.+) grabs your hand and throws you out of the room\.$')
  @running
  def throwsYou(self, match):
    if match[1] != self._target_name:
      return
    self.chain(self.MOVING, 'THROWN FROM ROOM')
    #self.chain(self.RESET, 'THROWN FROM ROOM')

  @bot.trigger('You have reached your cmds/minute limit.  You have to wait, sorry...', matcher=bot.SimpleMatcher)
  @running
  def cmdsMin(self, match):
    self.engine.startTimer('chain', 1.0, self.chain, self.RESET, 'CMDS/MINUTE LIMIT')

  @bot.trigger('What ?', matcher=bot.SimpleMatcher)
  @running
  @action(MOVING)
  def what(self, match):
    now = time.time()
    self._whats.append(now)
    self._whats = [x for x in self._whats if x >= now - 5]
    if len(self._whats) < 5:
      return
    self.chain(self.RESET, 'WHAT WHAT WHAT WHAT WHAT')

  @bot.trigger('Your legs run away with you.', matcher=bot.SimpleMatcher)
  @running
  def wimpy(self, match):
    self.chain(self.RESET, 'WIMPY', force=True)

  @bot.trigger(r'^Central square \(')
  def centralSquare(self, match):
    pass

  def loop(self):
    random.shuffle(self._areas)
    for area in self._areas:
      if not area or not area.hasValidNpcs(
          self.options.min_size, self.options.max_size):
        continue
      self.deposit()
      self._area = area
      for path in area.paths:
        yield path
      self._area = None
      self.sell()

  @running
  def next(self, rooms=1):
    if not self._iterator:
      self._iterator = self.loop()
    try:
      path = self._iterator.next()
      self.send(path)
      self.send('get')
    except StopIteration:
      self.chain(self.SPENDING, 'END OF LOOP')

  def lockTarget(self):
    if not self._target:
      return

    self._target_name = None
    self.send('pity %s' % self._target.id)
    self.send('scan %s' % self._target.id)

  def killTarget(self):
    if not self._target:
      return

    if self.options.kill or self._target.moves:
      self.send('kill %s' % self._target.id)

    self.send("%s '%s' %s" % (
        self.options.action, self.options.sksp, self._target.id))

  @running
  def chain(self, action, reason, force=False):
    self.engine.killTimer('chain')

    if self._stunned and action != self.STUNNED:
      self._action = self.STUNNED
      self._last_action = action
      self.chain(self.STUNNED, reason)
      return

    self._action = action

    if action in (self.KILLING, self.OTHER, self.SEARCHING, self.SCANNING) and (
        self._prompt['hp'] < self._prompt['maxhp'] * 0.80):
      self.chain(self.TICKING, reason)
      return

    if action == self.MOVING:
      self.status('RUNNING TO THE NEXT ROOM: %s', reason)
      self.next()
      return

    if action == self.SPENDING:
      self.status('SPENDING EXP: %s', reason)
      self.spend()
      return

    if action == self.SCANNING:
      self.status('CHECKING THE TARGETS HEALTH: %s', reason)
      self.lockTarget()
      return

    if action == self.KILLING:
      self.status('KILLING THE TARGET: %s', reason)
      self.killTarget()
      return

    if action == self.OTHER:
      self._target = None
      self._target_name = None
      self.chain(self.SEARCHING, reason)
      return

    if action == self.SEARCHING:
      self.status('SCANNING AREA AGAIN FOR TARGETS: %s', reason)
      self._target = None
      self._target_name = None
      self.send('bl;get')
      return

    if action == self.TICKING:
      self.status('NOT ENOUGH HPS, SLEEPING: %s', reason)
      return

    if action == self.STUNNED:
      self.status('WAITING FOR UNSTUNED: %s', reason)
      return

    if action == self.RESET:
      if not force:
        last_reset = time.time() - self._last_reset
        if last_reset < MIN_RESET:
          self.chain(self.RESET_SLEEP, 'RESET TOO SOON')
          return
      self.status('RESETTING: %s', reason)
      self.send('summary')
      self.quit()
      return

    if action == self.RESET_SLEEP:
      self.status('RESET SLEEP: %s', reason)
      self.engine.startTimer('chain', 60.0, self.chain, self.RESET, 'RESET TOO SOON')
      return

  def quit(self):
    self.send('quit')
    self.send('y', escape=False)

  @bot.trigger('Get what?', matcher=bot.SimpleMatcher)
  @running
  @action(MOVING, SEARCHING)
  def doneMoving(self, unused_match):
    if self._players:
      self.chain(self.MOVING, 'PLAYER FOUND')
    elif not self._target:
      self.send('get all;drop all corpse')
      self.chain(self.MOVING, 'NO TARGETS SET')
    else:
      self.chain(self.SCANNING, 'SCANNING TARGET')

  @bot.trigger(r'^(.+) is (.+)\.$')
  @running
  @action(SCANNING)
  def scan(self, match):
    if match[1] != self._target_name:
      return

    if match[2] == 'in good shape':
      self.chain(self.KILLING, 'TARGET UNHURT')
    else:
      self.chain(self.MOVING, 'DAMAGED TARGET')


  #@bot.trigger('You break your skill attempt.', matcher=bot.SimpleMatcher)
  @bot.trigger('You are stunned and unable to perform any action.', matcher=bot.SimpleMatcher)
  @bot.trigger('You are stunned and unable to fight.', matcher=bot.SimpleMatcher)
  def stunned(self, matcher):
    self._stunned = True

  @bot.trigger('You break out from the stun.', matcher=bot.SimpleMatcher)
  @running
  def unstunned(self, matcher):
    self._stunned = False
    if self._action == self.STUNNED:
      self.chain(self._last_action, 'UNSTUNNED')
      self._last_action = self.RESET
      return

    if self._action == self.KILLING:
      self.send("%s '%s'" % (self.options.action, self.options.sksp))
      return

  @bot.trigger('That is not possible.', matcher=bot.SimpleMatcher)
  def scanFail(self, match):
    # Scan target missing
    self.scanTargetMissing(match)

  @bot.trigger('Missing person or misspelled word 2', matcher=bot.SimpleMatcher)
  @bot.trigger('Need person for verb pity.', matcher=bot.SimpleMatcher)
  @running
  @action(SCANNING)
  def scanTargetMissing(self, match):
    # Pity target missing
    self.chain(self.SEARCHING, 'TARGET MISSING')

  @bot.trigger(r'^You feel sorry for (.+)\.$')
  @running
  @action(SCANNING)
  def pity(self, match):
    self._target_name = match[1]

  @bot.trigger(r'^A Huge Post office \(')
  def postOffice(self, unused_match):
    pass


  @bot.trigger(' \\(\x1b\\[1m[a-z]+\x1b\\[0m(,\x1b\\[1m[a-z]+\x1b\\[0m)*\\)\\.$', priority=-1, raw=True)
  @bot.trigger(r'There (are|is) [a-z]+ obvious exits?: ')
  @running
  @action(SEARCHING, MOVING)
  def room(self, unused_match):
    self._players = False
    self._target = None
    self._target_name = None

  @bot.trigger('(\x1b\\[35m)+([^\x1b]+)\x1b\\[2;37;0m', raw=True)
  @running
  @action(SEARCHING, MOVING)
  def npc(self, match):
    if self._target:
      return
    if not self._area:
      return
    target = self._area.npcs.get(match[2])
    if not target or not target.isValid(
        self.options.min_size, self.options.max_size):
      return
    self._target = target

  @bot.trigger('\x1b\\[31m.+\x1b\\[2;37;0m', raw=True)
  @bot.trigger('\x1b\\[35mGhost of ([a-z]+)\x1b\\[2;37;0m', raw=True)
  def lookPlayers(self, match):
    self._players = True

  @bot.trigger(r'^([A-Z][a-z]+) (arrives|floats in) ')
  @bot.trigger(r'^([A-Z][a-z]+) fades in\.$')
  @bot.trigger(r'^([A-Z][a-z]+) rises from the ground\.$')
  def arrives(self, match):
    player = match[1].lower()

  #@bot.trigger(r'^([A-Z][a-z]+) disappears in ')
  #@bot.trigger(r'^([A-Z][a-z]+) (leaves|floats)( [a-z0-9]+)?\.$')
  @bot.trigger(r'^(.+) leaves( [a-z0-9-]+)?\.$')
  @running
  @action(SCANNING)
  def leaves(self, match):
    if match[1] != self._target_name:
      return
    self.chain(self.OTHER, 'TARGET LEFT')

  @bot.trigger('You are not in combat.', matcher=bot.SimpleMatcher)
  @bot.trigger('Use * at who?', matcher=bot.GlobMatcher)
  @bot.trigger('Cast * at what?', matcher=bot.GlobMatcher)
  @running
  @action(KILLING)
  def notInCombat(self, match):
    self._target = None
    self._target_name = None
    self.chain(self.OTHER, 'TARGET MISSING')

  @bot.trigger('Target is not present.', matcher=bot.SimpleMatcher)
  @running
  @action(KILLING)
  def targetNotPresent(self, match):
    self._target = None
    self._target_name = None
    self.chain(self.SEARCHING, 'TARGET MISSING')

  @bot.trigger(r'^No (.+) here !$')
  @running
  @action(KILLING)
  def notHere(self, match):
    if match[1] != self._target.id:
      return
    self._target = None
    self._target_name = None
    self.chain(self.SEARCHING, 'TARGET MISSING')

  @bot.trigger(r'^([A-Z][a-z]+) is DEAD, R\.I\.P\.')
  @running
  @action(KILLING)
  def dead(self, match):
    if match[1] != self._target_name:
      return
    self._target = None
    self._target_name = None
    self.send(
        'get all scroll;keep all scroll;'
        'get all parchment;keep all parchment;'
        'get weapons;get armour;'
        'get all gold;'
        'drop all box;'
        'get corpse;eat corpse;eat all from ground')
    self.chain(self.OTHER, 'TARGET KILLED')

  @bot.trigger('*NEW ROUND*', matcher=bot.SimpleMatcher)
  def newRound(self, match):
    self.send('scan')

  def attackerCheck(self):
    now = time.time()
    self._foreign_attackers.append(now)
    self._foreign_attackers = [
        x for x in self._foreign_attackers if x >= now - 30]
    if len(self._foreign_attackers) >= 2:
      for _ in xrange(10):
        self.chain(self.MOVING, 'GETTING CHASED')
      return
    self.chain(self.MOVING, 'FOREIGN ATTACKER')

  @bot.trigger(r'^(.+) attacks ([A-Z][a-z]+)\.$')
  @running
  def attacksYou(self, match):
    if match[1].lower() == self.options.username or self._action == self.MOVING:
      return
    self.attackerCheck()

  @bot.trigger(r'^(.+) hits you \d+ times\.$')
  @running
  def hitsYou(self, match):
    if match[1] == self._target_name:
      return
    self.attackerCheck()

  @bot.trigger('You die.', matcher=bot.SimpleMatcher)
  def youDie(self, match):
    self.stopBot()

  @bot.trigger('You are magically transfered somewhere.', matcher=bot.SimpleMatcher)
  def wizSummon(self, match):
    self.stopBot()

  @bot.trigger('You fail miserably.', matcher=bot.SimpleMatcher)
  @bot.trigger('You fail the spell.', matcher=bot.SimpleMatcher)
  @bot.trigger('You have trouble concentrating and fail the spell.', matcher=bot.SimpleMatcher)
  @bot.trigger('You lose your balance and stumble, ruining the spell.', matcher=bot.SimpleMatcher)
  @bot.trigger('You lose your concentration and fail the spell.', matcher=bot.SimpleMatcher)
  @bot.trigger('You poke yourself in the eye and the spell misfires.', matcher=bot.SimpleMatcher)
  @bot.trigger('Your spell just fizzles.', matcher=bot.SimpleMatcher)
  @bot.trigger('Your spell just sputters.', matcher=bot.SimpleMatcher)
  @bot.trigger('You scream with frustration as the spell utterly fails.', matcher=bot.SimpleMatcher)
  @bot.trigger('You stumble over the spell\'s complexity and mumble the words.', matcher=bot.SimpleMatcher)
  @bot.trigger('You stutter the magic words and fail the spell.', matcher=bot.SimpleMatcher)
  @bot.trigger('You think of Leper and become too scared to cast your spell.', matcher=bot.SimpleMatcher)
  @bot.trigger('^[A-Z][a-z]+ completely resists the effects of your spell!$')
  def failSpell(self, unused_match):
    pass

  RESPONSES = [
      'no thanks',
      "i'm good, thanks",
      'a little busy',
      'maybe tomorrow',
      "can't now",
      'in the middle of something',
      'i have to go',
      ]

  @bot.trigger('^([A-Z][a-z]+) tells you')
  @running
  def tellsYou(self, match):
    player = match[1].lower()
    if player in WIZARDS or 'test' in player:
      self.stopBot()
      return
    if player == self.options.username:
      return
    if player not in self._talked:
      self.engine.startTimer('party', 2, self.send, 'tell %s %s' % (
          player, random.choice(self.RESPONSES)))
      self._talked.add(player)

  @bot.trigger(r'^You tell ([A-Z][a-z]+) ')
  @running
  def youTell(self, match):
    player = match[1].lower()
    self._talked.add(player)

#@bot.trigger('You feel yourself very strong and brave.', matcher=bot.SimpleMatcher)
#@bot.trigger('You have no \'berry\' to eat.', matcher=bot.SimpleMatcher)
#@bot.trigger('You are prepared to do the skill.', matcher=bot.SimpleMatcher)
#@bot.trigger('The berry decomposes.', matcher=bot.SimpleMatcher)
#@bot.trigger('You scout the surrounding area.', matcher=bot.SimpleMatcher)
#@bot.trigger('You watch the surroundings carefully.', matcher=bot.SimpleMatcher)
#@bot.trigger('You failed to concentrate enough to send the message.', matcher=bot.SimpleMatcher)
#@bot.trigger('You concentrate and mentally speak to your beast.', matcher=bot.SimpleMatcher)


#@bot.trigger('That is not possible.', matcher=bot.SimpleMatcher)
#@bot.trigger('Missing person or misspelled word 2', matcher=bot.SimpleMatcher)
#@bot.trigger(r'^(.+) is (.+)\.$')
#@bot.trigger(r'^You feel sorry for (.+)\.$')
#@bot.trigger(r'^(.+) is DEAD, R\.I\.P\.$')
#@bot.trigger(r"^There (are|is) (\d+) 'berry's? in your inventory\.$")


def defineFlags():
  parser = optparse.OptionParser(version='%prog v0.0', description=__doc__)
  # See: http://docs.python.org/library/optparse.html
  parser.add_option(
      '-v', '--verbosity',
      action='store',
      default=20,
      dest='verbosity',
      metavar='LEVEL',
      type='int',
      help='the logging verbosity')
  parser.add_option(
      '-l', '--log',
      action='store',
      default='killbot.log',
      dest='log',
      metavar='FILE',
      type='str',
      help='path to log file')
  parser.add_option(
      '-f', '--config',
      action='store',
      default='configs/settings.cfg',
      dest='config',
      metavar='FILE',
      type='str',
      help='path to the config file')
  parser.add_option(
      '-s', '--save',
      action='store',
      default='killbot.sav',
      dest='save',
      metavar='FILE',
      type='str',
      help='path to the killbot save file')
  parser.add_option(
      '-d', '--display',
      action='store_true',
      default=True,
      dest='display',
      help='display mud output to screen')
  parser.add_option(
      '-t', '--ttl',
      action='store',
      default=0,
      dest='ttl',
      metavar='SECONDS',
      type='int',
      help='time to live before killing')
  return parser.parse_args()


def main(options, unused_args):
  try:
    cfg = config.readConfig(options.config)
  except AssertionError, e:
    logging.error('%s', e)
    return os.EX_DATAERR
  options.address = cfg.get('server', 'address')
  options.port = int(cfg.get('server', 'port'))
  options.username = cfg.get('character', 'name')
  options.password = cfg.get('character', 'password')
  options.guild = cfg.get('settings', 'guild')
  options.action = cfg.get('settings', 'action')
  options.sksp = cfg.get('settings', 'sksp')
  options.kill = int(cfg.get('settings', 'kill'))
  options.min_size = int(cfg.get('settings', 'min_size'))
  options.max_size = int(cfg.get('settings', 'max_size'))

  trains = set(s[0] for s in cfg.items('trains') if s[1])
  areas = set(s[0] for s in cfg.items('areas') if int(s[1]))

  inst = KillBot(options, trains=trains, areas=areas)

  if options.ttl:
    inst.engine.startTimer('shutdown', options.ttl, inst.engine.shutdown)

  inst.start()
  return os.EX_OK


if __name__ == '__main__':
  opts, args = defineFlags()
  logging.basicConfig(
      level=opts.verbosity,
      datefmt='%Y/%m/%d %H:%M:%S',
      format='[%(asctime)s] %(levelname)s: %(message)s')
  sys.exit(main(opts, args))
