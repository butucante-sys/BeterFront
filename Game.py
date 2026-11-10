"""
OpenFront World - an OpenFront-style territory war game on a detailed world map.

Controls
  Left-click land ........ attack it (land you border)
  Right-click land ....... menu: Attack / Send boat / Request alliance / Betray
  Mouse wheel / slider ... % of your troops to send
  Ctrl + mouse wheel ..... zoom in/out   (+ / - keys also work)
  Right-drag / WASD ...... move around the map
  1-9, 0, N / buttons ... City, Defense, Silo, Air Def, Port, Station, Airport, Warship, Jet, Upgrade, Nuke
  Esc / right-click ...... cancel build mode or close the menu
  P pause   Ctrl+R restart

Features
  - Real satellite map of Earth (needs earth_day.jpg and earth_height.png next to this file;
    without them a generated map is used). 1600x622 tiles, real coastlines and mountains
  - Transport boats and cargo ships
  - Air Defense upgrades (level 1-8): every level widens the protected dome
  - Ports: cargo ships trade with other nations' ports (80k per ship)
  - Railways: stations link into networks, and also link to nearby foreign stations.
    Oil-tanker trains run across the network (50k per train); trains into a foreign network trade with them.
    Each connected building makes trains come 10% more often.
    In Station mode you see how the station will connect before you place it.
  - Airports: planes fly between airports; each plane landing from another nation pays 125k
  - War stops trade: after an attack, no ships/trains/planes between the two nations
    until 60 seconds pass without attacks
  - Annexation: land fully enclosed by your territory joins your nation
  - Upgrades (level 1-8) for every building
  - Warships: steal non-allied cargo ships, sink invasion boats, fight enemy warships
  - Nukes can target the sea and destroy ships
  - Fighter jets (3M) capture planes from non-allied nations mid-air
  - 10 weak tribes that only expand; eliminate anyone to loot 70% of their gold
  - Alliances (+25% trade between allies) and betrayal (traitor: -50% defense for 2 min)
"""
import subprocess
import sys

try:
    import pygame
except ImportError:
    print("Installing pygame into:", sys.executable)
    subprocess.check_call([sys.executable, "-m", "pip", "install", "pygame-ce"])
    import pygame

import base64
import gc
import os
import heapq
import math
import random
import time
import zlib
from collections import deque

# ---------------- Settings ----------------
GW, GH = 1600, 622          # map size in tiles (real Earth, 80N to 60S)
TS = 5                      # world pixels per tile
WORLD_W, WORLD_H = GW * TS, GH * TS
MAP_W, MAP_H = 1200, 600    # on-screen map view
PANEL_H = 110
WIN_W, WIN_H = MAP_W, MAP_H + PANEL_H
FPS = 60
TICK = 0.1                  # game logic step (seconds)
NUM_BOTS = 5
WIN_SHARE = 0.80            # own this share of the land to win
BOT_BOOST = 0.9             # bot troop growth multiplier (difficulty)

COST = {"city": 125_000, "defense": 50_000, "silo": 300_000, "airdef": 500_000, "port": 210_000,
        "station": 100_000, "airport": 10_000, "warship": 150_000, "jet": 3_000_000,
        "upgrade": 0, "nuke": 200_000}
START_GOLD = 15_000
LABEL = {"city": "City", "defense": "Defense", "silo": "Silo", "airdef": "Air Def", "port": "Port",
         "station": "Station", "airport": "Airport", "warship": "Warship", "jet": "Jet", "upgrade": "Upgrade", "nuke": "Nuke"}
MODES = ["city", "defense", "silo", "airdef", "port", "station", "airport", "warship", "jet", "upgrade", "nuke"]
MODE_KEYS = "1234567890N"
BUILDINGS = ["city", "defense", "silo", "airdef", "port", "station", "airport"]
RAIL_KINDS = ("station", "city", "port", "airport")
BUILD_GAP = 27              # min distance between buildings (tiles)

# economy
TROOPS_PER_TILE = 0.46
GROWTH_PER_TILE = 0.001
GOLD_BASE = 20              # gold per tick (0.1 s) every nation gets
GOLD_PER_TILE = 0.02        # gold per tick per tile owned
GOLD_PER_CITY = 80          # gold per tick per city

NUKE_RADIUS = 67
SILO_COOLDOWN = 8.0
DEFENSE_RANGE = 46

AD_BASE_RANGE = 93          # air defense range at level 1 (tiles)
AD_RANGE_STEP = 19          # extra range per level
AD_MAX_LEVEL = 8
AD_UPGRADE_COST = 100_000   # x current level
AD_COOLDOWN = 2.5
AD_HIT_CHANCE = 0.75

BOAT_SPEED = 46             # tiles per second (transport boats)
TRADE_SPEED = 33            # tiles per second (cargo ships)
MAX_BOATS = 3
TRADE_INTERVAL = 20.0      # seconds between cargo ships per port

RAIL_RANGE = 185            # max track length (tiles)
TRAIN_BASE_INTERVAL = 12.0
TRAIN_BONUS = 0.10          # +10% train frequency per connected building
TRAIN_SPEED = 91              # 25% slower oil tankers
MAX_TRAINS = 12

PLANE_INTERVAL = 90.0       # seconds between flights per airport
PLANE_SPEED = 133           # tiles per second
PLANE_REWARD = 125_000      # gold when a plane lands from another nation
TRAIN_REWARD = 50_000       # gold per train arrival (both nations on a cross-border trip)
PORT_REWARD = 80_000        # gold per cargo ship arrival (both nations)

PEACE_AFTER = 60.0          # seconds without attacks before trade resumes

MAX_LEVEL = 8               # every building can be upgraded to level 8
UPGRADE_FREQ = 0.25         # +25% planes / ships / trains per level
UPGRADE_INFO = {
    "city": "+2k max troops, +800 gold/s",
    "defense": "+15% area, +10% strength",
    "silo": "reloads 15% faster",
    "airdef": "wider dome",
    "port": "cargo ships 25% more often",
    "station": "trains 25% more often",
    "airport": "planes 25% more often",
}

WARSHIP_SPEED = 54          # tiles per second
WARSHIP_RANGE = 100         # how far a warship can see (tiles)
WARSHIP_PATROL = 116        # patrol radius around its home port
WARSHIP_LEASH = 231         # gives up a chase this far from home
WARSHIP_HP = 100
WARSHIPS_PER_PORT = 3

JET_SPEED = 289             # tiles per second (planes fly 69)
JET_RANGE = 212             # how far a jet can spot planes (tiles)
JET_PATROL = 174            # patrol radius around its airport
JET_LEASH = 424
JETS_PER_AIRPORT = 2

NUM_TRIBES = 25
TRIBE_BOOST = 0.5           # tribes grow troops at half speed
LOOT_SHARE = 0.70           # share of gold taken when you eliminate someone
TRIBE_NAMES = [n + " Tribe" for n in (
    "Orra", "Kesh", "Tamu", "Vala", "Nori", "Ishka", "Rumo", "Belu", "Sarn", "Okko", "Dara", "Feni", "Golo",
    "Hesk", "Ivo", "Jarn", "Kuro", "Lema", "Mosi", "Nabu", "Opa", "Pesh", "Quro", "Rani", "Sefu")]
TRIBE_COLORS = [(110 + (i * 37) % 70, 95 + (i * 23) % 55, 70 + (i * 41) % 50) for i in range(NUM_TRIBES)]

TRAITOR_TIME = 120.0        # seconds a betrayer is marked as traitor
ALLY_TRADE_BONUS = 1.25     # +25% trade income between allies

WATER = (38, 84, 145)
WATER_DEEP = (18, 44, 90)
COAST = (64, 122, 180)
LAKE = (60, 110, 170)
BOT_NAMES = ["Red Baron", "Atlantis", "Nordheim", "Sultanate", "Kraken", "Iron Union", "Zephyria"]
PLAYER_COLORS = [(60, 140, 255), (225, 60, 60), (250, 180, 30), (150, 70, 190),
                 (20, 180, 170), (120, 200, 70), (255, 120, 60)]
NB4 = ((1, 0), (-1, 0), (0, 1), (0, -1))
NB8 = NB4 + ((1, 1), (1, -1), (-1, 1), (-1, -1))

# 1600x622 world land mask (80N .. 60S, matches the satellite image), zlib + base64 packed bits
WORLD_MASK = (
    "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"
    "f72/3l/vr/fX++v99f56f72/Nnn9f78/2A8="
)
MAP_TOP_LAT = 80.0
MAP_BOTTOM_LAT = -60.0
TEXTURE_FILE = "earth_day.jpg"      # satellite image, put next to this .py file
HEIGHT_FILE = "earth_height.png"    # elevation map, put next to this .py file

# Mountain ranges: (width in degrees, height, [(lat, lon), ...])
RANGES = [
    (2.2, 1.00, [(35.5, 72), (33, 77), (30, 81), (28, 86), (27.6, 92), (28, 97)]),          # Himalaya
    (5.5, 0.62, [(36, 79), (34, 86), (33, 93), (31, 98)]),                                  # Tibet
    (2.0, 0.90, [(34.5, 68), (36, 72), (35.5, 77)]),                                        # Hindu Kush
    (2.0, 0.80, [(41.5, 70), (42.5, 78), (43, 86)]),                                        # Tian Shan
    (2.0, 0.70, [(50, 84), (48, 90), (46, 97)]),                                            # Altai
    (1.8, 0.60, [(51, 94), (52, 101)]),                                                     # Sayan
    (2.2, 0.75, [(37, 45), (33, 48), (29, 53), (27, 57)]),                                  # Zagros
    (1.6, 0.60, [(36.5, 50), (36, 57)]),                                                    # Alborz
    (1.5, 0.85, [(43.5, 40), (42.5, 45), (41, 48)]),                                        # Caucasus
    (2.0, 0.60, [(37.5, 31), (38.5, 36), (39.5, 42)]),                                      # Anatolia
    (1.4, 0.90, [(44, 7), (46, 8), (47, 11), (47, 14)]),                                    # Alps
    (1.0, 0.70, [(42.8, -1.5), (42.6, 2)]),                                                 # Pyrenees
    (1.6, 0.55, [(49.5, 19), (48, 24), (46, 25), (45.5, 23)]),                              # Carpathians
    (2.0, 0.60, [(59, 6), (62, 8), (66, 14), (69, 19)]),                                    # Scandinavia
    (1.5, 0.55, [(51, 59), (56, 59), (61, 59), (67, 63)]),                                  # Urals
    (2.5, 0.55, [(62, 128), (67, 132), (71, 136)]),                                         # Verkhoyansk
    (2.0, 0.60, [(52, 157), (60, 162)]),                                                    # Kamchatka
    (2.0, 0.70, [(30, -9), (32, -5), (35, 2), (36, 8)]),                                    # Atlas
    (3.0, 0.70, [(13, 38), (9, 39), (6, 38)]),                                              # Ethiopia
    (2.0, 0.60, [(-3, 37), (-8, 35)]),                                                      # East Africa
    (2.0, 0.60, [(-28, 29), (-31, 27)]),                                                    # Drakensberg
    (2.0, 0.55, [(19, 73.5), (13, 75), (9, 77)]),                                           # Western Ghats
    (2.0, 0.65, [(-4, 136), (-6, 143), (-7, 147)]),                                         # New Guinea
    (1.5, 0.70, [(34, 133), (36, 138), (40, 140), (43, 143)]),                              # Japan
    (3.5, 0.85, [(60, -136), (55, -125), (50, -116), (45, -111), (40, -106), (35, -106)]),  # Rockies
    (1.8, 0.75, [(48, -121), (42, -122), (37, -119)]),                                      # Cascades/Sierra
    (2.5, 0.70, [(30, -108), (24, -105), (19, -100), (17, -96)]),                           # Sierra Madre
    (2.5, 0.80, [(62, -152), (61, -145), (60, -140)]),                                      # Alaska Range
    (2.0, 0.50, [(34, -85), (38, -80), (42, -75), (45, -71)]),                              # Appalachians
    (2.2, 1.00, [(10, -73), (5, -76), (0, -78), (-6, -78), (-12, -76), (-17, -70),
                 (-23, -67), (-30, -70), (-38, -71), (-45, -72), (-52, -73)]),              # Andes
    (2.0, 0.55, [(-16, 145), (-23, 148), (-30, 151), (-36, 148), (-38, 146)]),              # Great Dividing
    (1.2, 0.75, [(-42, 172), (-45, 169)]),                                                  # NZ Alps
]

DESERTS = [(14, 33, -17, 60), (23, 38, 50, 75), (36, 48, 75, 115), (-32, -18, 117, 145),
           (24, 37, -118, -103), (-28, -18, 14, 25), (-50, -18, -75, -66)]


def fmt(n):
    n = int(n)
    if n >= 1_000_000:
        return f"{n / 1_000_000:.2f}M"
    return f"{n / 1000:.1f}k" if n >= 1000 else str(n)


def lerp_color(a, b, t):
    t = max(0.0, min(1.0, t))
    return tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


def tile_lat_lon(x, y):
    lat = MAP_TOP_LAT - (y + 0.5) * (MAP_TOP_LAT - MAP_BOTTOM_LAT) / GH
    lon = -180 + (x + 0.5) * 360 / GW
    return lat, lon


def tile_of(lat, lon):
    return (lon + 180) / 360 * GW, (MAP_TOP_LAT - lat) / (MAP_TOP_LAT - MAP_BOTTOM_LAT) * GH


def asset_path(name):
    """Find an image file next to this script (or in the current folder)."""
    dirs = [os.getcwd()]
    try:
        dirs.insert(0, os.path.dirname(os.path.abspath(__file__)))
    except NameError:
        pass
    for d in dirs:
        path = os.path.join(d, name)
        if os.path.exists(path):
            return path
    return None


def load_height():
    path = asset_path(HEIGHT_FILE)
    if not path:
        return None
    try:
        img = pygame.image.load(path)
        if img.get_size() != (GW, GH):
            return None
        to_bytes = getattr(pygame.image, "tobytes", None) or pygame.image.tostring
        raw = to_bytes(img, "RGB")
    except Exception as exc:
        print("Could not read", path, exc)
        return None
    return [[raw[(y * GW + x) * 3] / 255 for x in range(GW)] for y in range(GH)]


# ---------------- Map generation ----------------
def value_noise(cell):
    def smooth(t):
        return t * t * (3 - 2 * t)
    cw, ch = GW // cell + 2, GH // cell + 2
    grid = [[random.random() for _ in range(cw)] for _ in range(ch)]
    out = [[0.0] * GW for _ in range(GH)]
    for y in range(GH):
        gy = y / cell
        y0 = int(gy)
        fy = smooth(gy - y0)
        g0, g1, row = grid[y0], grid[y0 + 1], out[y]
        for x in range(GW):
            gx = x / cell
            x0 = int(gx)
            fx = smooth(gx - x0)
            a = g0[x0] + (g0[x0 + 1] - g0[x0]) * fx
            b = g1[x0] + (g1[x0 + 1] - g1[x0]) * fx
            row[x] = a + (b - a) * fy
    return out


def biome(lat, lon):
    if abs(lat) > 70:
        return "ice", (226, 230, 234)
    if abs(lat) > 62:
        return "tundra", (170, 180, 162)
    for la0, la1, lo0, lo1 in DESERTS:
        if la0 <= lat <= la1 and lo0 <= lon <= lo1:
            return "desert", (214, 192, 132)
    if abs(lat) < 12:
        return "jungle", (62, 128, 60)
    if abs(lat) > 50:
        return "taiga", (92, 132, 86)
    return "plains", (128, 170, 92)


def mountain_map(land):
    elev = [[0.0] * GW for _ in range(GH)]
    for width, height, pts in RANGES:
        tp = [tile_of(la, lo) for la, lo in pts]
        lat_mid = sum(p[0] for p in pts) / len(pts)
        w = width * GW / 360
        for (x0, y0), (x1, y1) in zip(tp, tp[1:]):
            dx, dy = x1 - x0, y1 - y0
            l2 = dx * dx + dy * dy or 1e-9
            for y in range(max(0, int(min(y0, y1) - w)), min(GH - 1, int(max(y0, y1) + w)) + 1):
                row, lrow = elev[y], land[y]
                for x in range(max(0, int(min(x0, x1) - w)), min(GW - 1, int(max(x0, x1) + w)) + 1):
                    if not lrow[x]:
                        continue
                    t = max(0.0, min(1.0, ((x - x0) * dx + (y - y0) * dy) / l2))
                    d = math.hypot(x - x0 - t * dx, y - y0 - t * dy)
                    if d < w:
                        v = height * (1 - (d / w) ** 2)
                        if v > row[x]:
                            row[x] = v
    return elev


def flood_sizes(grid_ok, nbrs):
    """Label connected regions where grid_ok is True; returns (labels, sizes)."""
    lab = [[-1] * GW for _ in range(GH)]
    sizes = []
    for y in range(GH):
        for x in range(GW):
            if grid_ok[y][x] and lab[y][x] < 0:
                cid = len(sizes)
                lab[y][x] = cid
                stack, n = [(x, y)], 0
                while stack:
                    cx, cy = stack.pop()
                    n += 1
                    for dx, dy in nbrs:
                        nx, ny = cx + dx, cy + dy
                        if 0 <= nx < GW and 0 <= ny < GH and grid_ok[ny][nx] and lab[ny][nx] < 0:
                            lab[ny][nx] = cid
                            stack.append((nx, ny))
                sizes.append(n)
    return lab, sizes


def terrain_colors(land, elev, coast):
    """Generated terrain colors - only used if the satellite image is missing."""
    n1, n2, n3 = value_noise(40), value_noise(14), value_noise(7)
    j1, j2 = value_noise(24), value_noise(24)
    height = [[(elev[y][x] + 0.18 * n1[y][x] + 0.07 * n3[y][x]) if land[y][x] else 0.0 for x in range(GW)]
              for y in range(GH)]
    colors = [[(0, 0, 0)] * GW for _ in range(GH)]
    for y in range(GH):
        for x in range(GW):
            if not land[y][x]:
                continue
            lat, lon = tile_lat_lon(x, y)
            kind, base = biome(lat + (j1[y][x] - 0.5) * 12 + (n3[y][x] - 0.5) * 4,
                               lon + (j2[y][x] - 0.5) * 16)
            e = elev[y][x]
            if e > 0.72:
                col = lerp_color((150, 138, 122), (242, 244, 248), (e - 0.72) / 0.18)
            elif e > 0.45:
                col = lerp_color(base, (142, 128, 110), (e - 0.45) / 0.27)
            elif e > 0.2:
                col = lerp_color(base, (122, 116, 90), 0.3 * (e - 0.2) / 0.25)
            else:
                col = base
            if coast[y][x] and abs(lat) < 55 and e < 0.4:
                col = lerp_color(col, (222, 206, 156), 0.5)
            hx0 = height[y][x - 1] if x > 0 else height[y][x]
            hx1 = height[y][x + 1] if x < GW - 1 else height[y][x]
            hy0 = height[y - 1][x] if y > 0 else height[y][x]
            hy1 = height[y + 1][x] if y < GH - 1 else height[y][x]
            light = max(-0.4, min(0.4, ((hx1 - hx0) + (hy1 - hy0)) * 2.2))
            col = lerp_color(col, (255, 255, 255), light * 0.6) if light > 0 else lerp_color(col, (0, 0, 0), -light)
            colors[y][x] = col
    return colors


def generate_map():
    data = zlib.decompress(base64.b64decode("".join(WORLD_MASK)))
    land = [[bool((data[(y * GW + x) >> 3] >> (7 - ((y * GW + x) & 7))) & 1) for x in range(GW)]
            for y in range(GH)]
    coast = [[land[y][x] and any(not (0 <= x + dx < GW and 0 <= y + dy < GH) or not land[y + dy][x + dx]
                                 for dx, dy in NB4) for x in range(GW)] for y in range(GH)]
    hmap = load_height()
    satellite = hmap is not None and asset_path(TEXTURE_FILE) is not None
    if hmap is not None:
        elev = [[min(1.0, (hmap[y][x] ** 0.8) * 1.15) if land[y][x] else 0.0 for x in range(GW)]
                for y in range(GH)]
    else:
        raw = mountain_map(land)
        n2, n3 = value_noise(14), value_noise(7)
        elev = [[raw[y][x] * (0.55 + 0.6 * n2[y][x] + 0.3 * n3[y][x]) for x in range(GW)] for y in range(GH)]
    colors = None if satellite else terrain_colors(land, elev, coast)
    n1 = value_noise(40)
    rough = [[min(1.6, elev[y][x] * 1.5 + 0.2 * n1[y][x]) if land[y][x] else 0.0 for x in range(GW)]
             for y in range(GH)]
    comp, csizes = flood_sizes(land, NB4)
    comp_size = [[csizes[comp[y][x]] if land[y][x] else 0 for x in range(GW)] for y in range(GH)]
    water = [[not v for v in row] for row in land]
    wbody, wsizes = flood_sizes(water, NB8)
    return land, rough, coast, colors, comp_size, wbody, wsizes


# ---------------- Game objects ----------------
class Player:
    def __init__(self, pid, name, color, is_ai):
        self.id = pid
        self.name = name
        self.color = color
        self.fill = tuple(min(255, int(c * 0.8 + 45)) for c in color)
        self.dark = tuple(int(c * 0.5) for c in color)
        self.is_ai = is_ai
        self.troops = 0.0
        self.gold = 0.0
        self.tiles = set()
        self.border = set()
        self.sx = self.sy = 0
        self.alive = True
        self.ai_timer = random.uniform(0.5, 2.0)
        self.tribe = False
        self.last_hit_by = None
        self.nuke_timer = 0.0
        self.label_pos = None
        self.train_timer = 0.0


class Building:
    def __init__(self, kind, x, y):
        self.kind = kind
        self.x, self.y = x, y
        self.cooldown = 0.0
        self.level = 1
        self.angle = random.uniform(0, math.tau)
        self.sweep = random.uniform(0, math.tau)
        self.tracking = False
        self.trade_timer = random.uniform(2, TRADE_INTERVAL)
        self.plane_timer = random.uniform(5, 15)
        self.ships_out = 0
        self.cd_total = SILO_COOLDOWN

    @property
    def freq(self):
        return 1 + UPGRADE_FREQ * (self.level - 1)

    @property
    def pos(self):
        return (self.x * TS + TS // 2, self.y * TS + TS // 2)

    @property
    def range(self):
        return AD_BASE_RANGE + AD_RANGE_STEP * (self.level - 1)


class Attack:
    def __init__(self, attacker, target, troops):
        self.attacker = attacker
        self.target = target
        self.troops = troops
        self.front = None
        self.age = 0


class Boat:
    """Transport boat (kind='transport') or cargo ship (kind='trade')."""
    def __init__(self, kind, owner, path, speed, troops=0, landing=None, src=None, dst=None):
        self.kind = kind
        self.owner = owner
        self.path = path
        self.speed = speed
        self.troops = troops
        self.landing = landing
        self.src, self.dst = src, dst
        self.i = 0.0
        self.heading = 0.0
        self.done = False
        self.sunk = False
        self.hold = False
        self.stolen_by = None
        self.hp = 40.0

    def pos(self):
        i = min(int(self.i), len(self.path) - 1)
        j = min(i + 1, len(self.path) - 1)
        f = self.i - i
        (x0, y0), (x1, y1) = self.path[i], self.path[j]
        if (x1, y1) != (x0, y0):
            target = math.atan2(y1 - y0, x1 - x0)
            diff = (target - self.heading + math.pi) % math.tau - math.pi
            self.heading += diff * 0.15
        return ((x0 + (x1 - x0) * f) * TS + TS / 2, (y0 + (y1 - y0) * f) * TS + TS / 2)

    def update(self, dt):
        if self.hold:
            return
        self.i += self.speed * dt
        if self.i >= len(self.path) - 1:
            self.i = len(self.path) - 1
            self.done = True


class Warship:
    def __init__(self, owner, home, x, y):
        self.owner = owner
        self.home = home
        self.x, self.y = x, y
        self.hp = float(WARSHIP_HP)
        self.heading = random.uniform(0, math.tau)
        self.target = None
        self.wp = None
        self.stuck = 0.0
        self.firing = None
        self.dead = False


class Jet:
    def __init__(self, owner, home):
        self.owner = owner
        self.home = home
        self.x, self.y = home.pos
        self.heading = random.uniform(0, math.tau)
        self.target = None
        self.wp = None
        self.trail = []
        self.dead = False


class RailEdge:
    """One stretch of track between two buildings, following the tile grid."""
    def __init__(self, a, b, tiles):
        self.a, self.b = a, b
        self.tiles = tiles
        self.pts = corner_points(tiles)

    def pts_from(self, node):
        return self.pts if node is self.a else self.pts[::-1]


def corner_points(tiles):
    """Keep only the tiles where the track changes direction (world pixels)."""
    if len(tiles) < 2:
        return [(t[0] * TS + TS / 2, t[1] * TS + TS / 2) for t in tiles * 2][:2]
    out = [tiles[0]]
    for i in range(1, len(tiles) - 1):
        d0 = (tiles[i][0] - tiles[i - 1][0], tiles[i][1] - tiles[i - 1][1])
        d1 = (tiles[i + 1][0] - tiles[i][0], tiles[i + 1][1] - tiles[i][1])
        if d0 != d1:
            out.append(tiles[i])
    out.append(tiles[-1])
    return [(x * TS + TS / 2, y * TS + TS / 2) for x, y in out]


class Train:
    """Oil-tanker train following a route of rail nodes."""
    def __init__(self, owner, pts, reward, dest_owner):
        self.owner = owner
        self.pts = pts
        self.seg = [max(0.01, math.dist(a, b)) for a, b in zip(pts, pts[1:])]
        self.length = sum(self.seg)
        self.reward = reward
        self.dest_owner = dest_owner
        self.d = 0.0
        self.done = False

    def update(self, dt):
        self.d += TRAIN_SPEED * TS * dt
        if self.d >= self.length:
            self.done = True

    def point(self, back=0.0):
        d = max(0.0, min(self.length, self.d - back))
        for i, L in enumerate(self.seg):
            if d <= L or i == len(self.seg) - 1:
                a, b = self.pts[i], self.pts[i + 1]
                t = min(1.0, d / L)
                return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t), math.atan2(b[1] - a[1], b[0] - a[0])
            d -= L
        return self.pts[-1], 0.0


class Plane:
    def __init__(self, owner, src, dst):
        self.owner = owner
        self.src, self.dst = src, dst
        self.a, self.b = src.pos, dst.pos
        self.length = max(1.0, math.dist(self.a, self.b))
        self.heading = math.atan2(self.b[1] - self.a[1], self.b[0] - self.a[0])
        self.d = 0.0
        self.done = False
        self.captured_by = None

    def update(self, dt):
        self.d += PLANE_SPEED * TS * dt
        if self.d >= self.length:
            self.done = True

    def t(self):
        return min(1.0, self.d / self.length)

    def pos(self):
        t = self.t()
        return (self.a[0] + (self.b[0] - self.a[0]) * t, self.a[1] + (self.b[1] - self.a[1]) * t)


class Nuke:
    def __init__(self, owner, start, target_tile):
        self.owner = owner
        self.start = start
        self.tx, self.ty = target_tile
        self.end = (self.tx * TS + TS // 2, self.ty * TS + TS // 2)
        dist = math.dist(start, self.end)
        self.duration = 2.0 + dist / 400
        self.apex = max(40, min(60 + dist * 0.25, 320, min(start[1], self.end[1]) - 10))
        self.t = 0.0
        self.pos = start
        self.ground = start
        self.heading = -math.pi / 2
        self.trail = []
        self.dead = False

    def update(self, dt):
        self.t = min(1.0, self.t + dt / self.duration)
        t = self.t
        gx = self.start[0] + (self.end[0] - self.start[0]) * t
        gy = self.start[1] + (self.end[1] - self.start[1]) * t
        prev = self.pos
        self.ground = (gx, gy)
        self.pos = (gx, gy - math.sin(math.pi * t) * self.apex)
        if self.pos != prev:
            self.heading = math.atan2(self.pos[1] - prev[1], self.pos[0] - prev[0])
        self.trail.append(self.pos)
        if len(self.trail) > 45:
            self.trail.pop(0)


class Interceptor:
    def __init__(self, start, nuke, hit, color):
        self.pos = list(start)
        self.nuke = nuke
        self.hit = hit
        self.color = color
        self.speed = 600
        self.trail = []
        self.dead = False


# ---------------- Game ----------------
gc.set_threshold(50000, 50, 50)
_MAP_CACHE = None    # the world map is built once and reused on restart


class Game:
    def __init__(self):
        global _MAP_CACHE
        fresh = _MAP_CACHE is None
        if fresh:
            _MAP_CACHE = {"data": generate_map()}
        (self.land, self.rough, self.coast, self.colors, self.comp_size,
         self.wbody, self.wsizes) = _MAP_CACHE["data"]
        self.land_total = sum(row.count(True) for row in self.land)
        self.coast_tiles = [(x, y) for y in range(GH) for x in range(GW) if self.coast[y][x]]
        self.owner = [[-1] * GW for _ in range(GH)]
        names = random.sample(BOT_NAMES, NUM_BOTS)
        self.players = [Player(0, "You", PLAYER_COLORS[0], False)]
        for i in range(NUM_BOTS):
            self.players.append(Player(i + 1, names[i], PLAYER_COLORS[i + 1], True))
        for j in range(NUM_TRIBES):
            t = Player(NUM_BOTS + 1 + j, TRIBE_NAMES[j], TRIBE_COLORS[j], True)
            t.tribe = True
            self.players.append(t)
        self.buildings, self.attacks = [], []
        self.nukes, self.interceptors, self.effects, self.messages = [], [], [], []
        self.boats, self.trains, self.planes = [], [], []
        self.rails, self.rail_adj, self.rail_nodes = [], {}, {}
        self.route_cache = {}
        self.route_budget = 2
        self.trade_paths = {}
        self.path_jobs = []
        self.war = {}                 # (a, b) -> time of last attack
        self.warships = []
        self.jets = []
        self.allies = set()           # frozenset({a, b})
        self.traitor_until = {}
        self.incoming = []            # alliance offers to you: {"frm", "expires"}
        self.replies = []             # (time, from, to): bots answering requests
        self.last_proposal = {}
        self.war_notified = set()
        self.phase = "spawn"
        self.mode = None
        self.ratio = 0.3
        self.time = 0.0
        self.ticks = 0
        self.acc = 0.0
        self.label_timer = 0.0
        self.annex_turn = 0
        self.paused = False
        if fresh:
            self.base = None
            if self.colors is not None:
                self.base = pygame.Surface((GW, GH))
                self.draw_terrain()
            _MAP_CACHE["base"] = self.base
        else:
            self.base = _MAP_CACHE["base"]
        self.fill_alpha = 115 if self.base is None else 200
        self.terr = pygame.Surface((GW, GH), pygame.SRCALPHA)
        self.terr.fill((0, 0, 0, 0))
        if self.base is not None and fresh:
            print("Satellite images not found next to the script - using the generated map")
        self.spawn_bots()
        self.update_labels()
        # the map is millions of small objects: stop the garbage collector re-scanning them (avoids stutter)
        gc.collect()
        if hasattr(gc, "freeze"):
            gc.freeze()

    # ----- tiles -----
    def draw_terrain(self):
        dist = [[-1] * GW for _ in range(GH)]
        q = deque()
        for y in range(GH):
            for x in range(GW):
                if self.land[y][x]:
                    dist[y][x] = 0
                    q.append((x, y))
        while q:
            x, y = q.popleft()
            for dx, dy in NB8:
                nx, ny = x + dx, y + dy
                if 0 <= nx < GW and 0 <= ny < GH and dist[ny][nx] < 0:
                    dist[ny][nx] = dist[y][x] + 1
                    q.append((nx, ny))
        for y in range(GH):
            for x in range(GW):
                if self.land[y][x]:
                    self.base.set_at((x, y), self.colors[y][x])
                elif self.wsizes[self.wbody[y][x]] < 6000:
                    self.base.set_at((x, y), LAKE)
                elif dist[y][x] == 1:
                    self.base.set_at((x, y), COAST)
                else:
                    t = min(1.0, (dist[y][x] - 1) / 24)
                    self.base.set_at((x, y), lerp_color(WATER, WATER_DEEP, t))

    def update_tile(self, x, y):
        if not self.land[y][x]:
            return
        o = self.owner[y][x]
        if o < 0:
            self.terr.set_at((x, y), (0, 0, 0, 0))
            return
        p = self.players[o]
        edge = False
        for dx, dy in NB4:
            nx, ny = x + dx, y + dy
            if not (0 <= nx < GW and 0 <= ny < GH) or self.owner[ny][nx] != o:
                edge = True
                break
        if edge:
            p.border.add((x, y))
            self.terr.set_at((x, y), (*p.dark, 235))
        else:
            p.border.discard((x, y))
            self.terr.set_at((x, y), (*p.fill, self.fill_alpha))

    def set_owner(self, x, y, pid):
        old = self.owner[y][x]
        if old == pid:
            return
        if old >= 0:
            op = self.players[old]
            if pid >= 0:
                op.last_hit_by = pid
            op.tiles.discard((x, y))
            op.border.discard((x, y))
            op.sx -= x
            op.sy -= y
        self.owner[y][x] = pid
        if pid >= 0:
            np_ = self.players[pid]
            np_.tiles.add((x, y))
            np_.sx += x
            np_.sy += y
        self.update_tile(x, y)
        for dx, dy in NB4:
            nx, ny = x + dx, y + dy
            if 0 <= nx < GW and 0 <= ny < GH:
                self.update_tile(nx, ny)

    def owner_of(self, b):
        return self.owner[b.y][b.x]

    # ----- spawning -----
    def spawn_at(self, pid, x, y):
        for yy in range(y - 4, y + 5):
            for xx in range(x - 4, x + 5):
                if (0 <= xx < GW and 0 <= yy < GH and self.land[yy][xx] and self.owner[yy][xx] < 0
                        and (xx - x) ** 2 + (yy - y) ** 2 <= 16):
                    self.set_owner(xx, yy, pid)
        p = self.players[pid]
        p.troops, p.gold = 600.0, float(START_GOLD)

    def spawn_bots(self):
        spots = []
        for p in self.players[1:]:
            big = 90 if p.tribe else 266
            for tries in range(4000):
                x, y = random.randrange(GW), random.randrange(GH)
                need = big if tries < 1500 else big * 0.6 if tries < 3000 else big * 0.3
                if (self.land[y][x] and self.comp_size[y][x] >= (750 if p.tribe else 4500)
                        and self.rough[y][x] < 0.6 and all(math.dist((x, y), s) >= need for s in spots)):
                    spots.append((x, y))
                    self.spawn_at(p.id, x, y)
                    if p.tribe:
                        p.troops = 300.0
                    break

    def try_player_spawn(self, x, y):
        if not self.land[y][x]:
            return "Pick a land tile"
        if self.comp_size[y][x] < 750:
            return "That island is too small - pick a bigger landmass"
        for yy in range(y - 40, y + 41):
            for xx in range(x - 40, x + 41):
                if 0 <= xx < GW and 0 <= yy < GH and self.owner[yy][xx] >= 0:
                    return "Too close to another nation"
        self.spawn_at(0, x, y)
        self.phase = "play"
        self.msg("You founded your nation. Expand!", (120, 220, 255))
        return None

    def msg(self, text, color=(255, 255, 255)):
        self.messages.append([text, self.time, color])
        self.messages = self.messages[-6:]

    # ----- war / trade embargo -----
    def mark_war(self, a, b):
        if a < 0 or b < 0 or a == b or self.is_ally(a, b):
            return
        key = (min(a, b), max(a, b))
        if 0 in key and self.can_trade(a, b):
            other = self.players[b if a == 0 else a]
            self.msg(f"At war with {other.name}: trade stopped", (255, 140, 90))
            self.war_notified.add(key)
        self.war[key] = self.time

    def can_trade(self, a, b):
        if a == b or self.is_ally(a, b):
            return True
        t = self.war.get((min(a, b), max(a, b)))
        return t is None or self.time - t >= PEACE_AFTER

    def war_left(self, a, b):
        t = self.war.get((min(a, b), max(a, b)))
        return 0 if t is None else max(0.0, PEACE_AFTER - (self.time - t))

    # ----- alliances & betrayal -----
    def is_ally(self, a, b):
        return a != b and frozenset((a, b)) in self.allies

    def allies_of(self, a):
        return [o for o in range(len(self.players)) if self.is_ally(a, o)]

    def is_traitor(self, pid):
        return pid >= 0 and self.time < self.traitor_until.get(pid, -1.0)

    def form_alliance(self, a, b):
        self.allies.add(frozenset((a, b)))
        self.war.pop((min(a, b), max(a, b)), None)
        self.war_notified.discard((min(a, b), max(a, b)))
        self.attacks = [x for x in self.attacks if not ({x.attacker, x.target} == {a, b})]
        if 0 in (a, b):
            other = self.players[b if a == 0 else a]
            self.msg(f"Alliance formed with {other.name}!", (140, 255, 170))

    def request_alliance(self, frm, to):
        if to < 0 or to == frm:
            return "Pick another nation"
        if self.players[to].tribe or self.players[frm].tribe:
            return "Tribes don't make alliances"
        if self.is_ally(frm, to):
            return "You are already allies"
        if self.is_traitor(frm):
            return "Nobody trusts a traitor right now"
        if not self.players[to].alive:
            return "That nation is gone"
        if to == 0:
            if not any(r["frm"] == frm for r in self.incoming):
                self.incoming.append({"frm": frm, "expires": self.time + 20})
            return None
        if any(r[1] == frm and r[2] == to for r in self.replies):
            return "Request already sent"
        self.replies.append((self.time + 1.5, frm, to))
        if frm == 0:
            self.msg(f"Alliance request sent to {self.players[to].name}...", (200, 230, 255))
        return None

    def decide_alliance(self, frm, to):
        """Bot `to` answers an alliance request from `frm`."""
        p, q = self.players[frm], self.players[to]
        if not (p.alive and q.alive) or self.is_ally(frm, to):
            return
        if self.is_traitor(frm) or not self.can_trade(frm, to):
            accept = False
        else:
            ratio = len(p.tiles) / max(1, len(q.tiles))
            chance = 0.75 if ratio < 1.5 else 0.45
            if len(self.allies_of(to)) >= 2:
                chance *= 0.4
            accept = random.random() < chance
        if accept:
            self.form_alliance(frm, to)
        elif frm == 0:
            why = " (you are a traitor)" if self.is_traitor(0) else " (you are at war)" if not self.can_trade(0, to) else ""
            self.msg(f"{q.name} rejected your alliance{why}.", (255, 170, 140))

    def respond_incoming(self, accept):
        if not self.incoming:
            return
        req = self.incoming.pop(0)
        other = self.players[req["frm"]]
        if accept and other.alive:
            self.form_alliance(0, req["frm"])
        else:
            self.msg(f"You rejected the alliance with {other.name}.", (200, 200, 210))

    def betray(self, a, b):
        if not self.is_ally(a, b):
            return "You are not allies"
        self.allies.discard(frozenset((a, b)))
        self.traitor_until[a] = self.time + TRAITOR_TIME
        pa, pb = self.players[a], self.players[b]
        if a == 0:
            self.msg(f"You betrayed {pb.name}! You are a TRAITOR for {int(TRAITOR_TIME)}s (-50% defense)",
                     (255, 150, 60))
        elif b == 0:
            self.msg(f"{pa.name} BETRAYED you!", (255, 80, 80))
        else:
            self.msg(f"{pa.name} betrayed {pb.name}!", (220, 200, 160))
        return None

    def update_diplomacy(self):
        due = [r for r in self.replies if r[0] <= self.time]
        self.replies = [r for r in self.replies if r[0] > self.time]
        for _, frm, to in due:
            self.decide_alliance(frm, to)
        keep = []
        for req in self.incoming:
            if req["expires"] <= self.time or not self.players[req["frm"]].alive:
                self.msg(f"Alliance offer from {self.players[req['frm']].name} expired", (190, 190, 200))
            else:
                keep.append(req)
        self.incoming = keep

    def check_peace(self):
        for key in list(self.war_notified):
            if self.can_trade(*key):
                self.war_notified.discard(key)
                other = self.players[key[1] if key[0] == 0 else key[0]]
                if other.alive:
                    self.msg(f"Peace with {other.name}: trade resumed", (140, 255, 170))

    # ----- economy -----
    def counts(self, pid):
        c = {k: 0 for k in BUILDINGS}
        for b in self.buildings:
            if self.owner_of(b) == pid:
                c[b.kind] += 1
        return c

    def levels(self, pid, kind):
        return sum(b.level for b in self.buildings if b.kind == kind and self.owner_of(b) == pid)

    def max_troops(self, p):
        return 800 + len(p.tiles) * TROOPS_PER_TILE + self.levels(p.id, "city") * 2000

    def train_bonus(self, pid):
        st = sum(b.level - 1 for b in self.buildings if b.kind == "station" and self.owner_of(b) == pid)
        return TRAIN_BONUS * self.rail_nodes.get(pid, 0) + UPGRADE_FREQ * st

    # ----- land attacks -----
    def frontier(self, pid, target):
        out = set()
        owner, land = self.owner, self.land
        for x, y in self.players[pid].border:
            for dx, dy in NB4:
                nx, ny = x + dx, y + dy
                if 0 <= nx < GW and 0 <= ny < GH and land[ny][nx] and owner[ny][nx] == target:
                    out.add((nx, ny))
        return out

    def borders(self, pid, target):
        owner, land = self.owner, self.land
        for x, y in self.players[pid].border:
            for dx, dy in NB4:
                nx, ny = x + dx, y + dy
                if 0 <= nx < GW and 0 <= ny < GH and land[ny][nx] and owner[ny][nx] == target:
                    return True
        return False

    def neighbours(self, p):
        found = set()
        for x, y in p.border:
            for dx, dy in NB4:
                nx, ny = x + dx, y + dy
                if 0 <= nx < GW and 0 <= ny < GH and self.land[ny][nx]:
                    o = self.owner[ny][nx]
                    if o != p.id:
                        found.add(o)
        return found

    def add_attack(self, pid, target, amount):
        for a in self.attacks:
            if a.attacker == pid and a.target == target:
                a.troops += amount
                a.front = None
                return
        self.attacks.append(Attack(pid, target, amount))

    def send_attack(self, pid, target, ratio):
        p = self.players[pid]
        if target == pid:
            return "That's already your land"
        if self.is_ally(pid, target):
            return f"{self.players[target].name} is your ally - betray them first (right-click)"
        if not self.borders(pid, target):
            return "You don't border that territory"
        amount = p.troops * ratio
        if amount < 5:
            return "Not enough troops"
        p.troops -= amount
        self.add_attack(pid, target, amount)
        self.mark_war(pid, target)
        if target == 0:
            self.msg(f"{p.name} is attacking you!", (255, 110, 110))
        return None

    def tile_cost(self, defender, x, y, posts):
        r = self.rough[y][x]
        if defender is None:
            return (1.0 + r * 2.5) / 7.5
        density = defender.troops / max(1, len(defender.tiles))
        cost = (0.75 + r * 2.0) / 7.5 + density
        for px, py, r2, mult in posts:
            if (px - x) ** 2 + (py - y) ** 2 <= r2:
                cost *= mult
                break
        if self.is_traitor(defender.id):
            cost *= 0.5
        return cost

    def process_attack(self, a):
        att = self.players[a.attacker]
        if not att.alive:
            return False
        if a.target >= 0 and self.is_ally(a.attacker, a.target):
            att.troops += a.troops
            return False
        if a.front is None or a.age % 30 == 0:
            a.front = self.frontier(a.attacker, a.target)
        a.age += 1
        if not a.front or a.troops < 1:
            att.troops += a.troops
            return False
        owner, land = self.owner, self.land
        cand = a.front if len(a.front) <= 300 else random.sample(tuple(a.front), 300)
        scored = []
        dead = []
        for (x, y) in cand:
            if owner[y][x] != a.target:
                dead.append((x, y))
                continue
            n = 0
            for dx, dy in NB4:
                nx, ny = x + dx, y + dy
                if 0 <= nx < GW and 0 <= ny < GH and owner[ny][nx] == a.attacker:
                    n += 1
            if n == 0:
                dead.append((x, y))
                continue
            scored.append((n + random.random() * 4.0 - self.rough[y][x] * 4, x, y))
        for t in dead:
            a.front.discard(t)
        if not scored:
            a.front = self.frontier(a.attacker, a.target)
            if not a.front:
                att.troops += a.troops
                return False
            return True
        scored.sort(reverse=True)
        k = min(len(scored), 2 + int(a.troops / 16), 260)
        defender = self.players[a.target] if a.target >= 0 else None
        posts = [(b.x, b.y, (DEFENSE_RANGE * (1 + 0.07 * (b.level - 1))) ** 2, 2.5 * (1 + 0.1 * (b.level - 1)))
                 for b in self.buildings
                 if b.kind == "defense" and defender and self.owner_of(b) == defender.id]
        if defender:
            self.war[(min(a.attacker, a.target), max(a.attacker, a.target))] = self.time
        for _, x, y in scored[:k]:
            cost = self.tile_cost(defender, x, y, posts)
            if a.troops < cost:
                att.troops += a.troops
                return False
            a.troops -= cost
            if defender:
                defender.troops = max(0.0, defender.troops - cost * 0.6)
            self.set_owner(x, y, a.attacker)
            a.front.discard((x, y))
            for dx, dy in NB4:
                nx, ny = x + dx, y + dy
                if 0 <= nx < GW and 0 <= ny < GH and land[ny][nx] and owner[ny][nx] == a.target:
                    a.front.add((nx, ny))
        return True

    # ----- sea: pathfinding, boats, trade -----
    def water_around(self, x, y):
        return [(x + dx, y + dy) for dx, dy in NB8
                if 0 <= x + dx < GW and 0 <= y + dy < GH and not self.land[y + dy][x + dx]]

    def astar(self, start, goals, target, limit=400000):
        """A* over water from start to any tile in goals. Generator: yields while working,
        returns the path start..goal (or None)."""
        tx, ty = target
        land = self.land
        g = {start: 0.0}
        prev = {start: None}
        heap = [(0.0, 0.0, start)]
        n = 0
        while heap:
            _, gc, c = heapq.heappop(heap)
            if c in goals:
                path = [c]
                while prev[c] is not None:
                    c = prev[c]
                    path.append(c)
                path.reverse()
                return path
            if gc > g[c]:
                continue
            n += 1
            if n > limit:
                return None
            if n % 200 == 0:
                yield
            cx, cy = c
            for dx, dy in NB8:
                nx, ny = cx + dx, cy + dy
                if not (0 <= nx < GW and 0 <= ny < GH) or land[ny][nx]:
                    continue
                ng = gc + (1.414 if dx and dy else 1.0)
                if ng < g.get((nx, ny), 1e18):
                    g[(nx, ny)] = ng
                    prev[(nx, ny)] = c
                    ax, ay = abs(nx - tx), abs(ny - ty)
                    h = max(ax, ay) + 0.414 * min(ax, ay)
                    heapq.heappush(heap, (ng + h * 1.3, ng, (nx, ny)))
        return None

    def run_path_jobs(self, budget=0.004):
        """Advance pending pathfinding jobs for at most `budget` seconds per frame."""
        t_end = time.perf_counter() + budget
        while self.path_jobs and time.perf_counter() < t_end:
            job = self.path_jobs[0]
            try:
                next(job["gen"])
            except StopIteration as done:
                self.path_jobs.pop(0)
                job["done"](done.value)

    def find_landing(self, tx, ty):
        o = self.owner[ty][tx]
        seen = {(tx, ty)}
        q = deque([(tx, ty)])
        while q and len(seen) < 15000:
            x, y = q.popleft()
            if self.coast[y][x] and self.water_around(x, y):
                return (x, y)
            for dx, dy in NB4:
                nx, ny = x + dx, y + dy
                if (0 <= nx < GW and 0 <= ny < GH and (nx, ny) not in seen
                        and self.land[ny][nx] and self.owner[ny][nx] == o):
                    seen.add((nx, ny))
                    q.append((nx, ny))
        return None

    def sea_route(self, pid, landing):
        """Path from the player's nearest coast (same sea) to the landing beach."""
        lw = self.water_around(*landing)
        bodies = {self.wbody[y][x] for x, y in lw}
        best = None
        for x, y in self.players[pid].border:
            if not self.coast[y][x]:
                continue
            d = (x - landing[0]) ** 2 + (y - landing[1]) ** 2
            if best is not None and d >= best[0]:
                continue
            for wx, wy in self.water_around(x, y):
                if self.wbody[wy][wx] in bodies:
                    best = (d, (wx, wy))
                    break
        if not best:
            return None
        return self.astar(best[1], set(lw), landing)  # generator

    def send_boat(self, pid, tx, ty, ratio):
        p = self.players[pid]
        if not self.land[ty][tx]:
            return "Click land to land a boat"
        target = self.owner[ty][tx]
        if target == pid:
            return "That's already your land"
        if self.is_ally(pid, target):
            return f"{self.players[target].name} is your ally"
        busy = sum(1 for b in self.boats if b.kind == "transport" and b.owner == pid)
        busy += sum(1 for j in self.path_jobs if j.get("boat_owner") == pid)
        if busy >= MAX_BOATS:
            return f"Max {MAX_BOATS} boats at sea"
        amount = p.troops * ratio
        if amount < 10:
            return "Not enough troops"
        landing = self.find_landing(tx, ty)
        if not landing:
            return "No beach to land on there"
        gen = self.sea_route(pid, landing)
        if gen is None:
            return "No sea route to that land"
        p.troops -= amount

        def done(path):
            if not path or not p.alive:
                p.troops += amount
                if pid == 0:
                    self.msg("No sea route to that land", (255, 160, 160))
                return
            self.boats.append(Boat("transport", pid, path, BOAT_SPEED, troops=amount, landing=landing))
            self.mark_war(pid, target)
            if target == 0:
                self.msg(f"{p.name} is sending boats at you!", (255, 110, 110))
            elif pid == 0:
                self.msg(f"Boat sent with {fmt(amount)} troops", (180, 220, 255))

        self.path_jobs.append({"gen": gen, "done": done, "boat_owner": pid})
        return None

    def land_boat(self, boat):
        p = self.players[boat.owner]
        x, y = boat.landing
        o = self.owner[y][x]
        if o == boat.owner:
            p.troops += boat.troops
            return
        self.set_owner(x, y, boat.owner)
        self.add_attack(boat.owner, o, boat.troops)
        self.mark_war(boat.owner, o)

    def request_trade_path(self, a, b):
        key = (id(a), id(b))
        self.trade_paths[key] = "pending"
        bw = self.water_around(b.x, b.y)
        bodies = {self.wbody[y][x] for x, y in bw}
        starts = [w for w in self.water_around(a.x, a.y) if self.wbody[w[1]][w[0]] in bodies]
        if not starts:
            self.trade_paths[key] = None
            return

        def done(path):
            self.trade_paths[key] = path
        self.path_jobs.append({"gen": self.astar(starts[0], set(bw), (b.x, b.y)), "done": done})

    def update_trade(self, dt):
        ports = [b for b in self.buildings if b.kind == "port" and self.owner_of(b) >= 0]
        for a in ports:
            if a.ships_out >= 1 + (a.level - 1) // 2:
                continue
            a.trade_timer -= dt
            if a.trade_timer > 0:
                continue
            a.trade_timer = TRADE_INTERVAL / a.freq
            oa = self.owner_of(a)
            partners = [b for b in ports
                        if self.owner_of(b) not in (oa, -1) and self.can_trade(oa, self.owner_of(b))]
            random.shuffle(partners)
            for b in partners[:3]:
                key = (id(a), id(b))
                if key not in self.trade_paths:
                    self.request_trade_path(a, b)
                    continue
                path = self.trade_paths[key]
                if path and path != "pending" and len(path) > 1:
                    a.ships_out += 1
                    self.boats.append(Boat("trade", oa, path, TRADE_SPEED, src=a, dst=b))
                    break

    def finish_trade(self, ship):
        if ship.stolen_by is not None:
            thief = ship.stolen_by
            if self.players[thief].alive:
                self.players[thief].gold += PORT_REWARD
                if thief == 0:
                    self.effects.append({"kind": "coin", "pos": ship.pos(), "t": 0.0, "dur": 1.5,
                                         "text": f"+{fmt(PORT_REWARD)} stolen"})
            return
        ship.src.ships_out = max(0, ship.src.ships_out - 1)
        oa, ob = self.owner_of(ship.src), self.owner_of(ship.dst)
        if ship.dst not in self.buildings or ob < 0 or oa < 0 or not self.can_trade(oa, ob):
            return
        reward = PORT_REWARD * (ALLY_TRADE_BONUS if self.is_ally(oa, ob) else 1)
        for o in {oa, ob}:
            self.players[o].gold += reward
        if 0 in (oa, ob):
            self.effects.append({"kind": "coin", "pos": ship.pos(), "t": 0.0, "dur": 1.2,
                                 "text": f"+{fmt(reward)}"})

    # ----- railways -----
    def rail_ok(self, x, y, allowed):
        return 0 <= x < GW and 0 <= y < GH and self.land[y][x] and self.owner[y][x] in allowed

    def l_route(self, a, b, allowed):
        """Tidy 45-degree route: a diagonal run plus a straight run (tries both orders)."""
        dx, dy = b.x - a.x, b.y - a.y
        sx, sy = (dx > 0) - (dx < 0), (dy > 0) - (dy < 0)
        diag = min(abs(dx), abs(dy))
        straight = max(abs(dx), abs(dy)) - diag
        st = (sx, 0) if abs(dx) > abs(dy) else (0, sy)
        for segs in (((sx, sy), diag, st, straight), (st, straight, (sx, sy), diag)):
            x, y = a.x, a.y
            tiles = [(x, y)]
            ok = True
            for (mx, my), n in ((segs[0], segs[1]), (segs[2], segs[3])):
                for _ in range(n):
                    x, y = x + mx, y + my
                    if not self.rail_ok(x, y, allowed):
                        ok = False
                        break
                    tiles.append((x, y))
                if not ok:
                    break
            if ok:
                return tiles
        return None

    def grid_route(self, a, b, allowed, limit=6000):
        """Grid path over allowed land that prefers straight runs and flat ground."""
        start, goal = (a.x, a.y), (b.x, b.y)
        g = {start: 0.0}
        prev = {start: None}
        heap = [(0.0, 0.0, start, -1)]
        n = 0
        while heap:
            _, gc, c, cd = heapq.heappop(heap)
            if c == goal:
                path = [c]
                while prev[c] is not None:
                    c = prev[c]
                    path.append(c)
                return path[::-1]
            if gc > g[c]:
                continue
            n += 1
            if n > limit:
                return None
            for i, (dx, dy) in enumerate(NB8):
                nx, ny = c[0] + dx, c[1] + dy
                if (nx, ny) != goal and not self.rail_ok(nx, ny, allowed):
                    continue
                if not (0 <= nx < GW and 0 <= ny < GH):
                    continue
                step = (1.414 if dx and dy else 1.0) * (1 + self.rough[ny][nx] * 1.5)
                ng = gc + step + (0.8 if cd >= 0 and i != cd else 0)
                if ng < g.get((nx, ny), 1e18):
                    g[(nx, ny)] = ng
                    prev[(nx, ny)] = c
                    ax, ay = abs(nx - goal[0]), abs(ny - goal[1])
                    heapq.heappush(heap, (ng + (max(ax, ay) + 0.414 * min(ax, ay)) * 1.2, ng, (nx, ny), i))
        return None

    def rail_route(self, a, b, allowed, cache=True):
        """Tiles from a to b, or None. Routes are cached and re-checked as borders move."""
        key = (id(a), id(b)) if id(a) < id(b) else (id(b), id(a))
        hit = self.route_cache.get(key) if cache else None
        if hit is not None:
            tiles, when = hit
            if tiles is None:
                if self.time - when < 10:
                    return None
            elif all(self.rail_ok(x, y, allowed) for x, y in tiles[1:-1]):
                return tiles if tiles[0] == (a.x, a.y) else tiles[::-1]
        tiles = self.l_route(a, b, allowed)
        if tiles is None:
            if cache and self.route_budget <= 0:
                return None          # out of time this round - try again next rebuild
            if cache:
                self.route_budget -= 1
            tiles = self.grid_route(a, b, allowed, 1500 if cache else 500)
        if cache:
            self.route_cache[key] = (None if tiles is None else
                                     (tiles if id(a) < id(b) else tiles[::-1]), self.time)
            if tiles is None:
                self.route_cache[key] = (None, self.time)
        return tiles

    def plan_links(self, s, so, stations, hubs, foreign, cache=True):
        """Links a new station at s would make: nearest own station, hubs that are
        closest to it, and the nearest foreign station. Returns [(building, tiles_or_None)]."""
        out = []
        R2 = RAIL_RANGE ** 2
        near = sorted((b for b in stations if b is not s and (b.x - s.x) ** 2 + (b.y - s.y) ** 2 <= R2),
                      key=lambda b: (b.x - s.x) ** 2 + (b.y - s.y) ** 2)
        for b in near[:3]:
            r = self.rail_route(s, b, {so}, cache)
            out.append((b, r))
            if r:
                break
        for h in hubs:
            d = (h.x - s.x) ** 2 + (h.y - s.y) ** 2
            if d > R2:
                continue
            if any((h.x - o.x) ** 2 + (h.y - o.y) ** 2 < d for o in stations if o is not s):
                continue
            out.append((h, self.rail_route(s, h, {so}, cache)))
        fnear = sorted((b for b in foreign if (b.x - s.x) ** 2 + (b.y - s.y) ** 2 <= R2),
                       key=lambda b: (b.x - s.x) ** 2 + (b.y - s.y) ** 2)
        for b in fnear[:2]:
            r = self.rail_route(s, b, {so, self.owner_of(b)}, cache)
            out.append((b, r))
            if r:
                break
        return out

    def rebuild_rails(self):
        edges, adj = [], {}
        self.route_budget = 1

        def add(a, b, tiles):
            e = RailEdge(a, b, tiles)
            edges.append(e)
            adj.setdefault(id(a), []).append((b, e))
            adj.setdefault(id(b), []).append((a, e))

        groups = {}
        for b in self.buildings:
            if b.kind in RAIL_KINDS:
                o = self.owner_of(b)
                if o >= 0:
                    groups.setdefault(o, ([], []))[0 if b.kind == "station" else 1].append(b)
        R2 = RAIL_RANGE ** 2
        for o, (stations, hubs) in groups.items():
            # stations: minimum spanning tree (shortest links first, no loops)
            parent = list(range(len(stations)))

            def find(i):
                while parent[i] != i:
                    parent[i] = parent[parent[i]]
                    i = parent[i]
                return i
            pairs = sorted(((a.x - b.x) ** 2 + (a.y - b.y) ** 2, i, j)
                           for i, a in enumerate(stations) for j, b in enumerate(stations)
                           if i < j and (a.x - b.x) ** 2 + (a.y - b.y) ** 2 <= R2)
            for _, i, j in pairs:
                ri, rj = find(i), find(j)
                if ri != rj:
                    tiles = self.rail_route(stations[i], stations[j], {o})
                    if tiles:
                        parent[ri] = rj
                        add(stations[i], stations[j], tiles)
            # each city / port / airport joins its nearest reachable station
            for h in hubs:
                for st in sorted((st for st in stations if (st.x - h.x) ** 2 + (st.y - h.y) ** 2 <= R2),
                                 key=lambda st: (st.x - h.x) ** 2 + (st.y - h.y) ** 2)[:3]:
                    tiles = self.rail_route(st, h, {o})
                    if tiles:
                        add(st, h, tiles)
                        break
        # one link from each station to the nearest foreign station (train trade)
        all_st = [b for b in self.buildings if b.kind == "station" and self.owner_of(b) >= 0]
        linked = set()
        for s in all_st:
            so = self.owner_of(s)
            cands = sorted((f for f in all_st if self.owner_of(f) != so
                            and (f.x - s.x) ** 2 + (f.y - s.y) ** 2 <= R2),
                           key=lambda f: (f.x - s.x) ** 2 + (f.y - s.y) ** 2)
            for f in cands[:2]:
                key = frozenset((id(s), id(f)))
                if key in linked or id(f) in {id(n) for n, e in adj.get(id(s), ())}:
                    break
                tiles = self.rail_route(s, f, {so, self.owner_of(f)})
                if tiles:
                    linked.add(key)
                    add(s, f, tiles)
                    break
        nodes = {}
        for b in self.buildings:
            if id(b) in adj:
                o = self.owner_of(b)
                if o >= 0:
                    nodes[o] = nodes.get(o, 0) + 1
        self.rails, self.rail_adj, self.rail_nodes = edges, adj, nodes
        if len(self.route_cache) > 4000:
            self.route_cache.clear()

    def spawn_train(self, p):
        starts = [b for b in self.buildings
                  if b.kind == "station" and id(b) in self.rail_adj and self.owner_of(b) == p.id]
        if not starts:
            return
        s = random.choice(starts)
        prev = {id(s): None}
        order = [s]
        q = deque([s])
        while q:
            c = q.popleft()
            for n, e in self.rail_adj.get(id(c), ()):
                if id(n) in prev:
                    continue
                on = self.owner_of(n)
                if on < 0 or (on != p.id and not self.can_trade(p.id, on)):
                    continue
                prev[id(n)] = (c, e)
                order.append(n)
                q.append(n)
        if len(order) < 2:
            return
        dest = random.choice(order[max(1, len(order) // 2):])
        hops, c = [], dest
        while prev[id(c)] is not None:
            par, e = prev[id(c)]
            hops.append((par, e))
            c = par
        hops.reverse()
        pts = []
        for par, e in hops:
            seg = e.pts_from(par)
            pts.extend(seg if not pts else seg[1:])
        if len(pts) >= 2:
            self.trains.append(Train(p.id, pts, TRAIN_REWARD, self.owner_of(dest)))

    def update_trains(self, dt):
        for p in self.players:
            if not p.alive or p.id not in self.rail_nodes:
                p.train_timer = 0.0
                continue
            p.train_timer += dt
            interval = TRAIN_BASE_INTERVAL / (1 + self.train_bonus(p.id))
            if p.train_timer >= interval:
                p.train_timer = 0.0
                if sum(1 for t in self.trains if t.owner == p.id) < MAX_TRAINS + 2 * self.levels(p.id, "station"):
                    self.spawn_train(p)
        for t in self.trains:
            t.update(dt)
            if not t.done:
                continue
            o, d = t.owner, t.dest_owner
            if not self.players[o].alive or not self.can_trade(o, d) or d < 0:
                continue
            reward = t.reward * (ALLY_TRADE_BONUS if self.is_ally(o, d) else 1)
            self.players[o].gold += reward
            text = f"+{fmt(reward)}"
            if d != o:
                self.players[d].gold += reward
                text += " trade"
            if 0 in (o, d):
                self.effects.append({"kind": "coin", "pos": t.pts[-1], "t": 0.0, "dur": 1.2, "text": text})
        self.trains = [t for t in self.trains if not t.done]

    # ----- airports -----
    def update_air(self, dt):
        airports = [b for b in self.buildings if b.kind == "airport" and self.owner_of(b) >= 0]
        for a in airports:
            a.plane_timer -= dt
            if a.plane_timer > 0:
                continue
            a.plane_timer = PLANE_INTERVAL / a.freq
            oa = self.owner_of(a)
            dests = [b for b in airports
                     if self.owner_of(b) != oa and self.can_trade(oa, self.owner_of(b))]
            if dests:
                self.planes.append(Plane(oa, a, random.choice(dests)))
        for pl in self.planes:
            pl.update(dt)
            if not pl.done:
                continue
            if pl.captured_by is not None:
                k = pl.captured_by
                if self.players[k].alive:
                    self.players[k].gold += PLANE_REWARD
                    if k == 0:
                        self.msg(f"Captured plane landed: +{fmt(PLANE_REWARD)} gold!", (255, 215, 80))
                        self.effects.append({"kind": "coin", "pos": pl.b, "t": 0.0, "dur": 1.8,
                                             "text": f"+{fmt(PLANE_REWARD)}"})
                continue
            od = self.owner_of(pl.dst) if pl.dst in self.buildings else -1
            if od < 0 or od == pl.owner or not self.can_trade(pl.owner, od):
                continue
            reward = PLANE_REWARD * (ALLY_TRADE_BONUS if self.is_ally(od, pl.owner) else 1)
            self.players[od].gold += reward
            if od == 0:
                self.msg(f"Plane from {self.players[pl.owner].name} landed: +{fmt(reward)} gold!",
                         (255, 215, 80))
                self.effects.append({"kind": "coin", "pos": pl.b, "t": 0.0, "dur": 1.8,
                                     "text": f"+{fmt(reward)}"})
        self.planes = [p for p in self.planes if not p.done]

    # ----- annexation -----
    def annex_player(self, p):
        if not p.tiles:
            return
        owner, land, coast = self.owner, self.land, self.coast
        visited = set()
        budget = 8000           # tiles examined per check, so big empires don't stall the game
        for x, y in list(p.border):
            if len(visited) > budget:
                break
            for dx, dy in NB4:
                sx, sy = x + dx, y + dy
                if (not (0 <= sx < GW and 0 <= sy < GH) or not land[sy][sx]
                        or owner[sy][sx] == p.id or (sx, sy) in visited):
                    continue
                o = owner[sy][sx]
                if o >= 0 and self.is_ally(p.id, o):
                    continue
                limit = 1500 if o < 0 else min(1500, len(p.tiles) // 2)
                comp, enclosed = [], True
                visited.add((sx, sy))
                q = deque([(sx, sy)])
                while q:
                    cx, cy = q.popleft()
                    comp.append((cx, cy))
                    if coast[cy][cx] or len(comp) > limit:
                        enclosed = False
                        break
                    for ex, ey in NB4:
                        nx, ny = cx + ex, cy + ey
                        if not (0 <= nx < GW and 0 <= ny < GH):
                            enclosed = False
                            break
                        if not land[ny][nx]:
                            continue
                        no = owner[ny][nx]
                        if no == o:
                            if (nx, ny) not in visited:
                                visited.add((nx, ny))
                                q.append((nx, ny))
                        elif no != p.id:
                            enclosed = False
                            break
                    if not enclosed:
                        break
                if not enclosed:
                    continue
                if o >= 0:
                    victim = self.players[o]
                    victim.troops *= max(0.0, 1 - len(comp) / max(1, len(victim.tiles)))
                for cx, cy in comp:
                    self.set_owner(cx, cy, p.id)
                if len(comp) < 10:
                    continue
                if p.id == 0:
                    who = "neutral land" if o < 0 else f"land from {self.players[o].name}"
                    self.msg(f"Annexed {len(comp)} tiles of {who}!", (140, 255, 170))
                elif o == 0:
                    self.msg(f"{p.name} annexed {len(comp)} of your tiles!", (255, 120, 120))

    # ----- buildings, upgrades & nukes -----
    def can_build(self, pid, kind, x, y):
        if not (0 <= x < GW and 0 <= y < GH) or self.owner[y][x] != pid:
            return "Build on your own land"
        if self.players[pid].gold < COST[kind]:
            return f"Not enough gold (need {fmt(COST[kind])})"
        if kind == "port" and not (self.coast[y][x] and self.water_around(x, y)):
            return "Ports must be on the coast"
        for b in self.buildings:
            if abs(b.x - x) < BUILD_GAP and abs(b.y - y) < BUILD_GAP:
                return "Too close to another building"
        return None

    def build(self, pid, kind, x, y):
        err = self.can_build(pid, kind, x, y)
        if err:
            return err
        self.players[pid].gold -= COST[kind]
        self.buildings.append(Building(kind, x, y))
        if kind in RAIL_KINDS:
            self.rebuild_rails()
        return None

    def airdef_near(self, pid, x, y):
        best, bd = None, 64
        for b in self.buildings:
            if b.kind == "airdef" and self.owner_of(b) == pid:
                d = (b.x - x) ** 2 + (b.y - y) ** 2
                if d <= bd:
                    best, bd = b, d
        return best

    def building_near(self, pid, x, y, kind=None, radius=8):
        best, bd = None, radius * radius
        for b in self.buildings:
            if (kind is None or b.kind == kind) and self.owner_of(b) == pid:
                d = (b.x - x) ** 2 + (b.y - y) ** 2
                if d <= bd:
                    best, bd = b, d
        return best

    def upgrade_cost(self, b):
        return COST[b.kind] // 2 * b.level

    def upgrade(self, pid, b):
        if b is None:
            return "Click one of your buildings to upgrade it"
        if b.level >= MAX_LEVEL:
            return f"{LABEL[b.kind]} is already max level {MAX_LEVEL}"
        cost = self.upgrade_cost(b)
        p = self.players[pid]
        if p.gold < cost:
            return f"Upgrade needs {fmt(cost)} gold"
        p.gold -= cost
        b.level += 1
        if pid == 0:
            extra = f" (range {b.range})" if b.kind == "airdef" else ""
            self.msg(f"{LABEL[b.kind]} upgraded to level {b.level}: {UPGRADE_INFO[b.kind]}{extra}", (140, 255, 200))
            r = b.range * TS if b.kind == "airdef" else 30
            self.effects.append({"kind": "ring", "pos": b.pos, "t": 0.0, "dur": 0.8, "r": r})
        if b.kind == "station":
            self.rebuild_rails()
        return None

    # ----- fighter jets -----
    def build_jet(self, pid, tx, ty):
        ap = self.building_near(pid, tx, ty, "airport", 10)
        if ap is None:
            return "Click one of your airports to launch a fighter jet"
        p = self.players[pid]
        if p.gold < COST["jet"]:
            return f"Not enough gold (need {fmt(COST['jet'])})"
        if sum(1 for j in self.jets if j.home is ap) >= JETS_PER_AIRPORT:
            return f"This airport already has {JETS_PER_AIRPORT} jets"
        p.gold -= COST["jet"]
        self.jets.append(Jet(pid, ap))
        if pid == 0:
            self.msg("Fighter jet launched!", (180, 220, 255))
        return None

    def plane_hostile(self, j, pl):
        if pl.done or pl.captured_by is not None or pl.owner == j.owner or self.is_ally(j.owner, pl.owner):
            return False
        do = self.owner_of(pl.dst) if pl.dst in self.buildings else -1
        return do != j.owner and not (do >= 0 and self.is_ally(j.owner, do))

    def fly(self, j, tx, ty, dt, speed=1.0, turn=5.0):
        want = math.atan2(ty - j.y, tx - j.x)
        diff = (want - j.heading + math.pi) % math.tau - math.pi
        j.heading += max(-turn * dt, min(turn * dt, diff))
        step = JET_SPEED * TS * dt * speed
        j.x = max(0.0, min(WORLD_W - 1.0, j.x + math.cos(j.heading) * step))
        j.y = max(0.0, min(WORLD_H - 1.0, j.y + math.sin(j.heading) * step))
        return math.dist((j.x, j.y), (tx, ty))

    def capture_plane(self, j, pl):
        victim = pl.owner
        x, y = pl.pos()
        pl.captured_by = j.owner
        pl.a, pl.b, pl.dst = (x, y), j.home.pos, j.home
        pl.length = max(1.0, math.dist(pl.a, pl.b))
        pl.d = 0.0
        pl.heading = math.atan2(pl.b[1] - y, pl.b[0] - x)
        self.mark_war(j.owner, victim)
        self.effects.append({"kind": "coin", "pos": (x, y), "t": 0.0, "dur": 1.2, "text": "Captured!"})
        if j.owner == 0:
            self.msg(f"Your jet captured a plane from {self.players[victim].name}!", (140, 255, 200))
        elif victim == 0:
            self.msg(f"{self.players[j.owner].name}'s fighter jet captured your plane!", (255, 120, 120))

    def update_jets(self, dt):
        for j in self.jets:
            if j.home not in self.buildings or self.owner_of(j.home) != j.owner:
                aps = [b for b in self.buildings if b.kind == "airport" and self.owner_of(b) == j.owner]
                if not aps:
                    j.dead = True
                    continue
                j.home = min(aps, key=lambda b: math.dist(b.pos, (j.x, j.y)))
            t = j.target
            if t is not None and (t not in self.planes or not self.plane_hostile(j, t)
                                  or math.dist((j.x, j.y), j.home.pos) > JET_LEASH * TS):
                j.target = t = None
            if t is None:
                reach = JET_RANGE * TS
                best = None
                for pl in self.planes:
                    if self.plane_hostile(j, pl):
                        d = math.dist((j.x, j.y), pl.pos())
                        if d <= reach and (best is None or d < best[0]):
                            best = (d, pl)
                j.target = t = best[1] if best else None
            if t is not None:
                px, py = t.pos()
                if self.fly(j, px, py, dt, 1.0, 6.0) < 3 * TS:
                    self.capture_plane(j, t)
                    j.target = None
            else:
                if j.wp is None or math.dist((j.x, j.y), j.wp) < 4 * TS:
                    a = random.uniform(0, math.tau)
                    r = random.uniform(10, JET_PATROL) * TS
                    hx, hy = j.home.pos
                    j.wp = (max(0, min(WORLD_W - 1, hx + math.cos(a) * r)), max(0, min(WORLD_H - 1, hy + math.sin(a) * r)))
                self.fly(j, *j.wp, dt, 0.45, 2.5)
            j.trail.append((j.x, j.y))
            if len(j.trail) > 18:
                j.trail.pop(0)
        self.jets = [j for j in self.jets if not j.dead]

    # ----- warships -----
    def build_warship(self, pid, tx, ty):
        port = self.building_near(pid, tx, ty, "port", 10)
        if port is None:
            return "Click one of your ports to launch a warship"
        p = self.players[pid]
        if p.gold < COST["warship"]:
            return f"Not enough gold (need {fmt(COST['warship'])})"
        if sum(1 for w in self.warships if w.home is port) >= WARSHIPS_PER_PORT:
            return f"This port already has {WARSHIPS_PER_PORT} warships"
        water = self.water_around(port.x, port.y)
        if not water:
            return "No water next to this port"
        wx, wy = water[0]
        p.gold -= COST["warship"]
        self.warships.append(Warship(pid, port, wx * TS + TS / 2, wy * TS + TS / 2))
        if pid == 0:
            self.msg("Warship launched!", (180, 220, 255))
        return None

    def is_water_px(self, x, y):
        tx, ty = int(x // TS), int(y // TS)
        return 0 <= tx < GW and 0 <= ty < GH and not self.land[ty][tx]

    def steer(self, w, tx, ty, dt, speed=1.0):
        dx, dy = tx - w.x, ty - w.y
        d = math.hypot(dx, dy)
        if d < 2:
            return True
        step = min(d, WARSHIP_SPEED * TS * dt * speed)
        base = math.atan2(dy, dx)
        for off in (0, 0.5, -0.5, 1.0, -1.0, 1.5, -1.5, 2.2, -2.2):
            a = base + off
            nx, ny = w.x + math.cos(a) * step, w.y + math.sin(a) * step
            if self.is_water_px(nx, ny):
                w.x, w.y = nx, ny
                diff = (a - w.heading + math.pi) % math.tau - math.pi
                w.heading += diff * 0.25
                return False
        w.stuck += dt
        return False

    def hostile(self, w, t):
        o = w.owner
        if isinstance(t, Warship):
            if t.dead or t.owner == o or self.is_ally(o, t.owner):
                return False
            tgt = t.target
            protecting = tgt is not None and (tgt.owner == o or (tgt.owner >= 0 and self.is_ally(o, tgt.owner)))
            return protecting or not self.can_trade(o, t.owner)
        if t.sunk or t.done or t.owner == o or self.is_ally(o, t.owner):
            return False
        if t.kind == "trade":
            return t.stolen_by is None and not t.hold
        lo = self.owner[t.landing[1]][t.landing[0]]
        return lo == o or (lo >= 0 and self.is_ally(o, lo))

    def find_target(self, w):
        best, bscore = None, None
        reach2 = (WARSHIP_RANGE * TS) ** 2
        for t in self.boats:
            if not self.hostile(w, t):
                continue
            x, y = t.pos()
            d2 = (x - w.x) ** 2 + (y - w.y) ** 2
            if d2 > reach2:
                continue
            score = d2 + (0 if t.kind == "transport" else 2 * reach2)
            if bscore is None or score < bscore:
                best, bscore = t, score
        for t in self.warships:
            if t is w or not self.hostile(w, t):
                continue
            d2 = (t.x - w.x) ** 2 + (t.y - w.y) ** 2
            if d2 > reach2:
                continue
            score = d2 + reach2
            if bscore is None or score < bscore:
                best, bscore = t, score
        return best

    def sink_boat(self, bt, by):
        bt.sunk = True
        x, y = bt.pos()
        self.effects.append({"kind": "sink", "pos": (x, y), "t": 0.0, "dur": 1.0})
        if bt.kind == "trade" and bt.stolen_by is None:
            bt.src.ships_out = max(0, bt.src.ships_out - 1)
        if bt.kind == "transport":
            if by == 0:
                self.msg(f"Your warship sank {self.players[bt.owner].name}'s invasion boat ({fmt(bt.troops)} troops)!",
                         (140, 255, 200))
            elif bt.owner == 0:
                self.msg(f"Your invasion boat was sunk by {self.players[by].name}!", (255, 120, 120))

    def steal(self, w, ship):
        victim = ship.owner
        if ship.stolen_by is None:
            ship.src.ships_out = max(0, ship.src.ships_out - 1)
        ship.stolen_by = w.owner
        ship.owner = w.owner
        ship.hold = True
        self.mark_war(w.owner, victim)
        x, y = ship.pos()
        if w.owner == 0:
            self.msg(f"Your warship captured a cargo ship from {self.players[victim].name}!", (140, 255, 200))
        elif victim == 0:
            self.msg(f"{self.players[w.owner].name}'s warship stole your cargo ship!", (255, 120, 120))
        self.effects.append({"kind": "coin", "pos": (x, y), "t": 0.0, "dur": 1.2, "text": "Captured!"})
        start = (int(x // TS), int(y // TS))
        home = w.home
        if self.land[start[1]][start[0]] or home not in self.buildings:
            ship.done = True
            return
        body = self.wbody[start[1]][start[0]]
        goals = {t for t in self.water_around(home.x, home.y) if self.wbody[t[1]][t[0]] == body}
        if not goals:
            ship.done = True
            return

        def done(path):
            if path and len(path) > 1:
                ship.path, ship.i, ship.hold, ship.dst = path, 0.0, False, home
            else:
                ship.done = True
        self.path_jobs.append({"gen": self.astar(start, goals, (home.x, home.y)), "done": done})

    def pick_waypoint(self, w):
        h = w.home
        water = self.water_around(h.x, h.y)
        body = self.wbody[water[0][1]][water[0][0]] if water else None
        for _ in range(30):
            a = random.uniform(0, math.tau)
            r = random.uniform(5, WARSHIP_PATROL)
            tx, ty = int(h.x + math.cos(a) * r), int(h.y + math.sin(a) * r)
            if 0 <= tx < GW and 0 <= ty < GH and not self.land[ty][tx] and self.wbody[ty][tx] == body:
                return (tx * TS + TS / 2, ty * TS + TS / 2)
        return (w.x, w.y)

    def update_warships(self, dt):
        for w in self.warships:
            if w.dead:
                continue
            if w.home not in self.buildings or self.owner_of(w.home) != w.owner:
                ports = [b for b in self.buildings if b.kind == "port" and self.owner_of(b) == w.owner]
                if ports:
                    w.home = min(ports, key=lambda b: math.dist(b.pos, (w.x, w.y)))
            w.firing = None
            t = w.target
            if t is not None:
                gone = (t.dead if isinstance(t, Warship) else (t.sunk or t.done or t not in self.boats))
                if gone or not self.hostile(w, t) or math.dist((w.x, w.y), w.home.pos) > WARSHIP_LEASH * TS:
                    w.target = t = None
            if t is None:
                w.target = t = self.find_target(w)
            if t is None:
                if w.wp is None or w.stuck > 2 or self.steer(w, *w.wp, dt, 0.6):
                    w.wp = self.pick_waypoint(w)
                    w.stuck = 0.0
                continue
            tx, ty = (t.x, t.y) if isinstance(t, Warship) else t.pos()
            d = math.dist((w.x, w.y), (tx, ty))
            if isinstance(t, Boat) and t.kind == "trade":
                if d < 2.5 * TS:
                    self.steal(w, t)
                    w.target = None
                else:
                    self.steer(w, tx, ty, dt)
                continue
            if d < 7 * TS:
                w.firing = (tx, ty)
                if isinstance(t, Warship):
                    t.hp -= 15 * dt
                    if t.hp <= 0 and not t.dead:
                        t.dead = True
                        self.effects.append({"kind": "sink", "pos": (t.x, t.y), "t": 0.0, "dur": 1.2})
                        self.mark_war(w.owner, t.owner)
                        if w.owner == 0:
                            self.msg(f"Your warship sank a {self.players[t.owner].name} warship!", (140, 255, 200))
                        elif t.owner == 0:
                            self.msg(f"Your warship was sunk by {self.players[w.owner].name}!", (255, 120, 120))
                    if d > 4 * TS:
                        self.steer(w, tx, ty, dt, 0.5)
                else:
                    t.hp -= 30 * dt
                    if t.hp <= 0 and not t.sunk:
                        self.sink_boat(t, w.owner)
                    self.steer(w, tx, ty, dt, 0.7)
            else:
                self.steer(w, tx, ty, dt)
        self.warships = [w for w in self.warships if not w.dead]

    def launch_nuke(self, pid, tx, ty):
        p = self.players[pid]
        if not (0 <= tx < GW and 0 <= ty < GH):
            return "Target is off the map"
        if self.land[ty][tx] and self.is_ally(pid, self.owner[ty][tx]):
            return "You can't nuke an ally"
        if p.gold < COST["nuke"]:
            return "Not enough gold"
        silos = [b for b in self.buildings
                 if b.kind == "silo" and self.owner_of(b) == pid and b.cooldown <= 0]
        if not silos:
            return "Need a ready Missile Silo"
        target_px = (tx * TS, ty * TS)
        silo = min(silos, key=lambda b: math.dist(b.pos, target_px))
        p.gold -= COST["nuke"]
        silo.cooldown = silo.cd_total = SILO_COOLDOWN * 0.85 ** (silo.level - 1)
        self.nukes.append(Nuke(pid, silo.pos, (tx, ty)))
        victim = self.owner[ty][tx]
        self.mark_war(pid, victim)
        vname = (self.players[victim].name if victim >= 0 else
                 "neutral land" if self.land[ty][tx] else "the sea")
        color = (255, 90, 90) if victim == 0 else (255, 200, 120)
        self.msg(f"{p.name} launched a NUKE at {vname}!", color)
        return None

    def detonate(self, nuke):
        r = NUKE_RADIUS
        lost, hit = {}, []
        for y in range(nuke.ty - r, nuke.ty + r + 1):
            for x in range(nuke.tx - r, nuke.tx + r + 1):
                if (0 <= x < GW and 0 <= y < GH and self.land[y][x]
                        and (x - nuke.tx) ** 2 + (y - nuke.ty) ** 2 <= r * r):
                    o = self.owner[y][x]
                    if o >= 0:
                        lost[o] = lost.get(o, 0) + 1
                    hit.append((x, y))
        for o in lost:
            if o != nuke.owner:
                self.players[o].last_hit_by = nuke.owner
        for o, n in lost.items():
            p = self.players[o]
            p.troops *= max(0.0, 1 - 1.2 * n / max(1, len(p.tiles)))
        for x, y in hit:
            self.set_owner(x, y, -1)
        self.buildings = [b for b in self.buildings
                          if (b.x - nuke.tx) ** 2 + (b.y - nuke.ty) ** 2 > r * r]
        self.rebuild_rails()
        rp2 = (r * TS) ** 2
        ships = 0
        for bt in self.boats:
            if bt.sunk:
                continue
            x, y = bt.pos()
            if (x - nuke.end[0]) ** 2 + (y - nuke.end[1]) ** 2 <= rp2:
                self.sink_boat(bt, nuke.owner)
                ships += 1
        for w in self.warships:
            if not w.dead and (w.x - nuke.end[0]) ** 2 + (w.y - nuke.end[1]) ** 2 <= rp2:
                w.dead = True
                ships += 1
                if w.owner != nuke.owner:
                    self.mark_war(nuke.owner, w.owner)
        if ships and nuke.owner == 0:
            self.msg(f"Nuke destroyed {ships} ship(s)!", (255, 200, 120))
        self.effects.append({"kind": "boom", "pos": nuke.end, "t": 0.0, "dur": 1.6})

    # ----- AI -----
    def ai_build(self, p, kind, tiles):
        if not tiles:
            return False
        for _ in range(15):
            x, y = random.choice(tiles)
            if self.build(p.id, kind, x, y) is None:
                return True
        return False

    def ai_boat(self, p):
        if sum(1 for b in self.boats if b.kind == "transport" and b.owner == p.id) >= 2:
            return
        if not p.label_pos:
            return
        sample = random.sample(self.coast_tiles, min(80, len(self.coast_tiles)))
        sample = [t for t in sample if self.owner[t[1]][t[0]] != p.id
                  and not self.is_ally(p.id, self.owner[t[1]][t[0]])]
        neutral = [t for t in sample if self.owner[t[1]][t[0]] < 0]
        pool = neutral or sample
        if not pool:
            return
        cx, cy = p.label_pos[0] / TS, p.label_pos[1] / TS
        tx, ty = min(pool, key=lambda t: (t[0] - cx) ** 2 + (t[1] - cy) ** 2)
        self.send_boat(p.id, tx, ty, 0.35)

    def ai_diplomacy(self, p):
        me = self.players[0]
        # propose an alliance to the human player
        if (me.alive and self.phase == "play" and not self.is_ally(p.id, 0) and self.can_trade(p.id, 0)
                and not self.is_traitor(0) and not self.is_traitor(p.id)
                and self.time - self.last_proposal.get(p.id, -999) > 90
                and len(self.allies_of(p.id)) < 2 and random.random() < 0.03):
            self.last_proposal[p.id] = self.time
            self.request_alliance(p.id, 0)
            self.msg(f"{p.name} proposes an alliance!", (200, 230, 255))
        # bots ally with each other
        if random.random() < 0.01 and len(self.allies_of(p.id)) < 2:
            others = [q for q in self.players[1:] if q.alive and q.id != p.id and not q.tribe
                      and not self.is_ally(p.id, q.id)]
            if others:
                self.request_alliance(p.id, random.choice(others).id)
        # betray a weak ally
        for a in self.allies_of(p.id):
            q = self.players[a]
            if q.troops < 0.4 * p.troops and random.random() < 0.03:
                self.betray(p.id, a)
                if self.borders(p.id, a):
                    self.send_attack(p.id, a, 0.5)
                break

    def tribe_think(self, p):
        """Tribes only expand and very rarely attack - they never build, sail or ally."""
        if p.troops < self.max_troops(p) * 0.4:
            return
        nbrs = self.neighbours(p)
        if -1 in nbrs:
            self.send_attack(p.id, -1, 0.25)
        elif random.random() < 0.05:
            enemies = [self.players[i] for i in nbrs if i >= 0]
            if enemies:
                self.send_attack(p.id, min(enemies, key=lambda q: q.troops).id, 0.2)

    def ai_think(self, p):
        mt = self.max_troops(p)
        n = len(p.tiles)
        tl = random.sample(tuple(p.tiles), min(400, n))
        c = self.counts(p.id)
        r = random.random()
        enemy_silos = any(b.kind == "silo" and self.owner_of(b) not in (-1, p.id) for b in self.buildings)

        if c["silo"] and p.gold > COST["nuke"] and self.time >= p.nuke_timer and random.random() < 0.25:
            rivals = [q for q in self.players if q.alive and q.id != p.id and q.tiles
                      and not self.is_ally(p.id, q.id)]
            if rivals:
                victim = max(rivals, key=lambda q: len(q.tiles))
                tx, ty = random.choice(tuple(victim.tiles))
                if self.launch_nuke(p.id, tx, ty) is None:
                    p.nuke_timer = self.time + 30

        my_ads = [b for b in self.buildings if b.kind == "airdef" and self.owner_of(b) == p.id]
        coast = [t for t in p.border if self.coast[t[1]][t[0]]]
        saving = c["silo"] and random.random() < 0.5
        if c["airport"] < 1 + n // 45000 and p.gold >= COST["airport"]:
            self.ai_build(p, "airport", tl)
        elif c["silo"] == 0 and n > 6000 and self.time > 120:
            if p.gold > COST["silo"]:
                self.ai_build(p, "silo", tl)
        elif saving and p.gold < COST["nuke"]:
            pass
        elif enemy_silos and c["airdef"] < 1 + n // 22700 and p.gold > COST["airdef"] and r < 0.5:
            self.ai_build(p, "airdef", tl)
        elif (my_aps := [b for b in self.buildings if b.kind == "airport" and self.owner_of(b) == p.id]) and \
                sum(1 for j in self.jets if j.owner == p.id) < len(my_aps) and \
                p.gold > COST["jet"] + 200_000 and r < 0.3:
            ap = random.choice(my_aps)
            self.build_jet(p.id, ap.x, ap.y)
        elif (my_ports := [b for b in self.buildings if b.kind == "port" and self.owner_of(b) == p.id]) and \
                sum(1 for w in self.warships if w.owner == p.id) < len(my_ports) and \
                p.gold > COST["warship"] + 50_000 and r < 0.35:
            port = random.choice(my_ports)
            self.build_warship(p.id, port.x, port.y)
        elif r < 0.3 and (ups := [b for b in self.buildings if self.owner_of(b) == p.id and b.level < MAX_LEVEL
                                   and b.kind in ("airport", "port", "airdef", "city", "station")]):
            b = min(ups, key=lambda b: (b.level, self.upgrade_cost(b)))
            if p.gold > self.upgrade_cost(b) + 50_000:
                self.upgrade(p.id, b)
        elif coast and c["port"] < 1 + n // 21000 and p.gold > COST["port"] and (c["port"] == 0 or r < 0.4):
            self.ai_build(p, "port", coast)
        elif c["station"] < 1 + n // 19000 and c["city"] + c["port"] >= 2 and p.gold > COST["station"]:
            hubs = [b for b in self.buildings if b.kind in ("city", "port") and self.owner_of(b) == p.id]
            hub = random.choice(hubs)
            near = [t for t in tl if abs(t[0] - hub.x) <= 83 and abs(t[1] - hub.y) <= 83]
            self.ai_build(p, "station", near)
        elif p.gold > COST["city"] + 10_000 and r < 0.45:
            self.ai_build(p, "city", tl)
        elif p.gold > COST["defense"] and r < 0.6 and p.border and c["defense"] < 1 + n // 7500:
            self.ai_build(p, "defense", random.sample(tuple(p.border), min(200, len(p.border))))

        self.ai_diplomacy(p)
        if p.troops < mt * 0.25:
            return
        nbrs = self.neighbours(p)
        if -1 in nbrs:
            self.send_attack(p.id, -1, 0.4)
        enemies = [self.players[i] for i in nbrs if i >= 0 and not self.is_ally(p.id, i)]
        if enemies:
            weakest = min(enemies, key=lambda q: q.troops)
            ratio_needed = 1.5 if -1 in nbrs else 0.6
            if p.troops * 0.5 > weakest.troops * ratio_needed or (-1 not in nbrs and random.random() < 0.4):
                self.send_attack(p.id, weakest.id, 0.5)
        if (-1 not in nbrs and random.random() < 0.3) or random.random() < 0.04:
            self.ai_boat(p)

    # ----- main logic step -----
    def tick(self):
        self.time += TICK
        self.ticks += 1
        for p in self.players:
            if not p.alive:
                continue
            n = len(p.tiles)
            mt = self.max_troops(p)
            if p.troops < mt:
                boost = TRIBE_BOOST if p.tribe else BOT_BOOST if p.is_ai else 1.0
                p.troops = min(mt, p.troops + (2 + n * GROWTH_PER_TILE) * (1 - p.troops / mt) * boost + 0.3)
            else:
                p.troops -= (p.troops - mt) * 0.02
            p.gold += GOLD_BASE + n * GOLD_PER_TILE + self.levels(p.id, "city") * GOLD_PER_CITY

        self.attacks = [a for a in self.attacks if self.process_attack(a)]

        self.update_diplomacy()
        if self.ticks % 10 == 0:
            self.rebuild_rails()
            self.check_peace()
        if self.ticks % 5 == 0:
            alive = [p for p in self.players if p.alive]
            if alive:
                self.annex_turn = (self.annex_turn + 1) % len(alive)
                self.annex_player(alive[self.annex_turn])

        for p in self.players:
            if (p.alive and not p.tiles and not any(b.owner == p.id and b.kind == "transport" for b in self.boats)
                    and not any(j.get("boat_owner") == p.id for j in self.path_jobs)):
                p.alive = False
                p.troops = 0
                k = p.last_hit_by
                if k is not None and k != p.id and self.players[k].alive and p.gold > 0:
                    loot = p.gold * LOOT_SHARE
                    self.players[k].gold += loot
                    p.gold = 0
                    if k == 0:
                        self.msg(f"You eliminated {p.name} and looted {fmt(loot)} gold!", (255, 215, 80))
                    else:
                        self.msg(f"{self.players[k].name} eliminated {p.name} (+{fmt(loot)} gold)", (255, 215, 90))
                else:
                    self.msg(f"{p.name} has been eliminated!", (255, 215, 90))

        for p in self.players[1:]:
            if p.alive:
                p.ai_timer -= TICK
                if p.ai_timer <= 0:
                    if p.tribe:
                        self.tribe_think(p)
                        p.ai_timer = random.uniform(2.0, 3.0)
                    else:
                        self.ai_think(p)
                        p.ai_timer = random.uniform(1.0, 1.8)

        self.label_timer -= TICK
        if self.label_timer <= 0:
            self.update_labels()
            self.label_timer = 1.0

        me = self.players[0]
        if not me.alive:
            self.phase = "lost"
        elif len(me.tiles) >= self.land_total * WIN_SHARE or not any(p.alive for p in self.players[1:] if not p.tribe):
            self.phase = "won"

    def update_labels(self):
        for p in self.players:
            if not p.tiles:
                p.label_pos = None
                continue
            n = len(p.tiles)
            cx, cy = p.sx / n, p.sy / n
            ix, iy = int(cx), int(cy)
            if not (0 <= ix < GW and 0 <= iy < GH) or self.owner[iy][ix] != p.id:
                pool = random.sample(tuple(p.tiles), min(400, n))
                ix, iy = min(pool, key=lambda t: (t[0] - cx) ** 2 + (t[1] - cy) ** 2)
            p.label_pos = (ix * TS + TS // 2, iy * TS + TS // 2)

    # ----- real-time projectiles & effects -----
    def update_realtime(self, dt):
        for b in self.buildings:
            b.cooldown = max(0.0, b.cooldown - dt)
            if b.kind == "airdef":
                b.sweep = (b.sweep + dt * 2.5) % math.tau
                b.tracking = False

        for nk in self.nukes:
            nk.update(dt)

        for b in self.buildings:
            if b.kind != "airdef":
                continue
            o = self.owner_of(b)
            if o < 0:
                continue
            reach = b.range * TS
            for nk in self.nukes:
                if nk.dead or nk.owner == o:
                    continue
                if math.dist(b.pos, nk.ground) <= reach:
                    b.tracking = True
                    b.angle = math.atan2(nk.pos[1] - b.pos[1], nk.pos[0] - b.pos[0])
                    if b.cooldown <= 0:
                        b.cooldown = AD_COOLDOWN
                        hit = random.random() < AD_HIT_CHANCE
                        self.interceptors.append(Interceptor(b.pos, nk, hit, self.players[o].color))
                    break
            if not b.tracking:
                b.angle = (b.angle + dt * 1.4) % math.tau

        for it in self.interceptors:
            nk = it.nuke
            if nk.dead or nk.t >= 1:
                it.dead = True
                self.effects.append({"kind": "puff", "pos": tuple(it.pos), "t": 0.0, "dur": 0.5})
                continue
            dx, dy = nk.pos[0] - it.pos[0], nk.pos[1] - it.pos[1]
            d = math.hypot(dx, dy)
            step = it.speed * dt
            it.trail.append(tuple(it.pos))
            if len(it.trail) > 14:
                it.trail.pop(0)
            if d <= step + 4:
                it.dead = True
                if it.hit:
                    nk.dead = True
                    self.effects.append({"kind": "intercept", "pos": nk.pos, "t": 0.0, "dur": 0.7})
                    if nk.owner == 0 or self.owner[nk.ty][nk.tx] == 0:
                        self.msg("Air defense intercepted a nuke!", (140, 255, 200))
                else:
                    self.effects.append({"kind": "puff", "pos": nk.pos, "t": 0.0, "dur": 0.5})
            else:
                it.pos[0] += dx / d * step
                it.pos[1] += dy / d * step

        for nk in self.nukes:
            if not nk.dead and nk.t >= 1:
                nk.dead = True
                self.detonate(nk)
        self.nukes = [n for n in self.nukes if not n.dead]
        self.interceptors = [i for i in self.interceptors if not i.dead]

        for bt in self.boats:
            if bt.sunk:
                continue
            bt.update(dt)
            if bt.done:
                if bt.kind == "transport":
                    self.land_boat(bt)
                else:
                    self.finish_trade(bt)
        self.update_warships(dt)
        self.update_jets(dt)
        self.boats = [b for b in self.boats if not b.done and not b.sunk]
        self.run_path_jobs()
        self.update_trade(dt)
        self.update_trains(dt)
        self.update_air(dt)

        for e in self.effects:
            e["t"] += dt
        self.effects = [e for e in self.effects if e["t"] < e["dur"]]

    def update(self, dt):
        if self.paused or self.phase != "play":
            return
        self.acc += dt
        while self.acc >= TICK:
            self.acc -= TICK
            self.tick()
            if self.phase != "play":
                break
        self.update_realtime(dt)


# ---------------- Drawing ----------------
MAX_ZOOM = 6.0
MIN_ZOOM = max(MAP_W / WORLD_W, MAP_H / WORLD_H)   # zoomed all the way out the map fills the window
ICON_BASE = 36            # building size in pixels at zoom 1
SS = 3                    # supersampling for smooth sprites
OUT = (38, 38, 46)        # outline color


def rot(cx, cy, ang, pts, scale=1.0):
    c, s = math.cos(ang), math.sin(ang)
    return [(cx + (x * c - y * s) * scale, cy + (x * s + y * c) * scale) for x, y in pts]


def darker(c, f=0.55):
    return tuple(int(v * f) for v in c)


def lighter(c, f=0.35):
    return tuple(int(v + (255 - v) * f) for v in c)


def star_points(cx, cy, r):
    pts = []
    for i in range(10):
        rr = r if i % 2 == 0 else r * 0.45
        a = -math.pi / 2 + i * math.pi / 5
        pts.append((cx + math.cos(a) * rr, cy + math.sin(a) * rr))
    return pts


class Camera:
    def __init__(self):
        self.z, self.ox, self.oy = MIN_ZOOM, (WORLD_W - MAP_W / MIN_ZOOM) / 2, 0.0

    def clamp(self):
        self.z = max(MIN_ZOOM, min(MAX_ZOOM, self.z))
        self.ox = max(0.0, min(WORLD_W - MAP_W / self.z, self.ox))
        self.oy = max(0.0, min(WORLD_H - MAP_H / self.z, self.oy))

    def w2s(self, x, y):
        return ((x - self.ox) * self.z, (y - self.oy) * self.z)

    def s2w(self, sx, sy):
        return (sx / self.z + self.ox, sy / self.z + self.oy)

    def zoom_at(self, sx, sy, factor):
        wx, wy = self.s2w(sx, sy)
        self.z = max(MIN_ZOOM, min(MAX_ZOOM, self.z * factor))
        self.ox, self.oy = wx - sx / self.z, wy - sy / self.z
        self.clamp()

    def pan(self, dx, dy):
        self.ox += dx / self.z
        self.oy += dy / self.z
        self.clamp()


class Sprites:
    """Detailed building art, drawn at 3x resolution in a 100x100 design box and smoothed down."""

    def __init__(self):
        self.cache = {}

    def get(self, kind, color, size, variant=0):
        size = max(10, int(size) // 2 * 2)
        key = (kind, color, size, variant)
        spr = self.cache.get(key)
        if spr is None:
            big = pygame.Surface((size * SS, size * SS), pygame.SRCALPHA)
            getattr(self, "draw_" + kind)(big, size * SS / 100, color, variant)
            spr = pygame.transform.smoothscale(big, (size, size))
            self.cache[key] = spr
        return spr

    # helpers in design units
    @staticmethod
    def R(k, x, y, w, h):
        return pygame.Rect(round(x * k), round(y * k), max(1, round(w * k)), max(1, round(h * k)))

    @staticmethod
    def P(k, pts):
        return [(x * k, y * k) for x, y in pts]

    @staticmethod
    def W(k, w):
        return max(1, round(w * k))

    def shadow(self, s, k, x=6, y=82, w=88, h=14):
        pygame.draw.ellipse(s, (0, 0, 0, 70), self.R(k, x, y, w, h))

    def box(self, s, k, color, x, y, w, h, outline=True, ow=1.2):
        pygame.draw.rect(s, color, self.R(k, x, y, w, h))
        if outline:
            pygame.draw.rect(s, OUT, self.R(k, x, y, w, h), self.W(k, ow))

    def poly(self, s, k, color, pts, outline=True, ow=1.2):
        pygame.draw.polygon(s, color, self.P(k, pts))
        if outline:
            pygame.draw.polygon(s, OUT, self.P(k, pts), self.W(k, ow))

    def line(self, s, k, color, a, b, w=1.0):
        pygame.draw.line(s, color, (a[0] * k, a[1] * k), (b[0] * k, b[1] * k), self.W(k, w))

    def circ(self, s, k, color, x, y, r, w=0):
        pygame.draw.circle(s, color, (x * k, y * k), max(1, r * k), self.W(k, w) if w else 0)

    # ---- City: skyline with lit windows ----
    def draw_city(self, s, k, c, v):
        lit, dim = (255, 214, 110), (95, 110, 135)
        self.shadow(s, k)
        self.box(s, k, (78, 78, 84), 2, 88, 96, 8, False)
        for i in range(5):
            self.box(s, k, (235, 235, 235), 6 + i * 19, 91, 9, 2, False)
        # tree
        self.box(s, k, (105, 72, 40), 5, 74, 3, 14, False)
        self.circ(s, k, (55, 125, 55), 6.5, 69, 8)
        self.circ(s, k, (85, 160, 80), 4.5, 66, 3.5)
        # left house
        self.box(s, k, (236, 228, 212), 13, 62, 19, 26)
        self.poly(s, k, c, [(10, 62), (22.5, 47), (35, 62)])
        self.poly(s, k, darker(c, 0.75), [(22.5, 47), (35, 62), (22.5, 62)], False)
        self.box(s, k, lit, 16, 67, 5, 5, False)
        self.box(s, k, lit, 25, 67, 5, 5, False)
        self.box(s, k, (110, 72, 42), 20, 77, 6, 11, False)
        # glass tower
        self.poly(s, k, (120, 136, 162), [(52, 14), (60, 19), (60, 88), (52, 88)])
        self.box(s, k, (172, 190, 214), 34, 14, 18, 74)
        self.box(s, k, c, 33, 9, 20, 6)
        self.line(s, k, (70, 70, 75), (43, 9), (43, 1), 1.2)
        self.circ(s, k, (240, 50, 50), 43, 2, 1.6)
        for row, y in enumerate(range(19, 84, 7)):
            for col, x in enumerate((37, 43, 48)):
                self.box(s, k, lit if (row * 3 + col) % 4 else dim, x, y, 3.2, 4, False)
        # brick block
        self.box(s, k, (186, 104, 76), 62, 42, 19, 46)
        for y in range(48, 88, 6):
            self.line(s, k, (150, 80, 58), (62.5, y), (80.5, y), 0.6)
        for y in range(47, 82, 10):
            self.box(s, k, (250, 228, 150), 65, y, 4, 5, False)
            self.box(s, k, (250, 228, 150), 73, y, 4, 5, False)
        self.box(s, k, c, 60, 38, 23, 5)
        # small house
        self.box(s, k, (226, 214, 190), 83, 68, 14, 20)
        self.poly(s, k, darker(c, 0.7), [(81, 68), (90, 57), (99, 68)])
        self.box(s, k, lit, 87, 73, 5, 5, False)

    # ---- Defense post: stone castle ----
    def draw_defense(self, s, k, c, v):
        stone, sd, sl = (172, 168, 158), (128, 124, 115), (196, 193, 183)
        self.shadow(s, k)
        # main wall with bricks
        self.box(s, k, stone, 20, 46, 60, 40, False)
        for i, y in enumerate(range(46, 86, 7)):
            self.line(s, k, sd, (20, y), (80, y), 0.7)
            for x in range(20 + (i % 2) * 6, 80, 12):
                self.line(s, k, sd, (x, y), (x, min(86, y + 7)), 0.7)
        pygame.draw.rect(s, OUT, self.R(k, 20, 46, 60, 40), self.W(k, 1.2))
        for i in range(5):
            self.box(s, k, stone, 22 + i * 12, 38, 8, 8)
        # towers
        for tx in (5, 75):
            self.box(s, k, sl, tx, 28, 20, 58, False)
            for y in range(34, 86, 7):
                self.line(s, k, sd, (tx, y), (tx + 20, y), 0.6)
            pygame.draw.rect(s, OUT, self.R(k, tx, 28, 20, 58), self.W(k, 1.2))
            for cx in (0, 7.5, 15):
                self.box(s, k, sl, tx + cx, 20, 5, 9)
            self.box(s, k, (35, 30, 30), tx + 8, 32, 4, 8, False)
            self.poly(s, k, c, [(tx + 4, 46), (tx + 16, 46), (tx + 16, 62), (tx + 10, 57), (tx + 4, 62)])
            self.circ(s, k, lighter(c, 0.6), tx + 10, 51, 2)
        # gate with portcullis
        self.circ(s, k, (55, 40, 30), 50, 66, 8)
        self.box(s, k, (55, 40, 30), 42, 66, 16, 20, False)
        for x in range(44, 57, 4):
            self.line(s, k, (120, 120, 125), (x, 60), (x, 86), 0.8)
        for y in range(64, 86, 5):
            self.line(s, k, (120, 120, 125), (42, y), (58, y), 0.8)
        # flag
        self.line(s, k, (70, 70, 70), (15, 20), (15, 1), 1.2)
        self.poly(s, k, c, [(15, 2), (24, 0), (33, 4), (33, 12), (24, 9), (15, 11)])

    # ---- Missile silo: bunker with blast doors ----
    def draw_silo(self, s, k, c, ready):
        self.shadow(s, k, 4, 84, 92, 12)
        self.box(s, k, (192, 192, 190), 6, 54, 88, 14)
        self.box(s, k, (150, 150, 150), 6, 68, 88, 20)
        self.box(s, k, c, 6, 70, 88, 5, False)
        s.set_clip(self.R(k, 6, 80, 88, 8))
        self.box(s, k, (245, 200, 40), 6, 80, 88, 8, False)
        for x in range(0, 100, 10):
            self.poly(s, k, (30, 30, 30), [(x, 88), (x + 5, 80), (x + 10, 80), (x + 5, 88)], False)
        s.set_clip(None)
        pygame.draw.rect(s, OUT, self.R(k, 6, 54, 88, 34), self.W(k, 1.2))
        pygame.draw.ellipse(s, (22, 22, 26), self.R(k, 28, 54, 44, 14))
        if ready:
            self.poly(s, k, (125, 128, 132), [(28, 61), (14, 40), (24, 35), (38, 57)])
            self.poly(s, k, (125, 128, 132), [(72, 61), (86, 40), (76, 35), (62, 57)])
            self.box(s, k, (242, 242, 242), 44, 12, 12, 50)
            self.box(s, k, (30, 30, 30), 44, 28, 12, 4, False)
            self.box(s, k, c, 44, 38, 12, 4, False)
            self.poly(s, k, (215, 40, 40), [(44, 12), (50, 0), (56, 12)])
            self.poly(s, k, (110, 110, 115), [(44, 50), (37, 60), (44, 60)])
            self.poly(s, k, (110, 110, 115), [(56, 50), (63, 60), (56, 60)])
            pygame.draw.rect(s, OUT, self.R(k, 44, 12, 12, 50), self.W(k, 1))
        else:
            pygame.draw.ellipse(s, (128, 130, 134), self.R(k, 28, 54, 44, 14))
            pygame.draw.ellipse(s, OUT, self.R(k, 28, 54, 44, 14), self.W(k, 1))
            self.line(s, k, (60, 60, 65), (50, 54), (50, 68), 1)

    # ---- Air defense: armored truck + mast (dish & launcher drawn rotating on top) ----
    def draw_airdef(self, s, k, c, v):
        self.shadow(s, k, 4, 84, 92, 12)
        self.poly(s, k, (96, 108, 80), [(8, 60), (92, 60), (97, 71), (92, 82), (8, 82), (3, 71)])
        self.box(s, k, (122, 132, 102), 10, 61, 80, 5, False)
        self.box(s, k, c, 6, 73, 88, 4, False)
        for x in (18, 36, 64, 82):
            self.circ(s, k, (32, 32, 36), x, 86, 8)
            self.circ(s, k, (150, 150, 155), x, 86, 3)
        self.box(s, k, (122, 126, 134), 46, 30, 8, 32)
        for y in range(34, 60, 8):
            self.line(s, k, (90, 94, 100), (46, y), (54, y + 6), 0.8)

    def draw_dish(self, s, k, c, v):
        outer = [(30 + q * q / 40, 50 + q) for q in range(-26, 27, 2)]
        inner = [(37 + q * q / 50, 50 + q) for q in range(26, -27, -2)]
        self.box(s, k, (128, 132, 138), 20, 45, 12, 10)
        self.circ(s, k, c, 24, 50, 4)
        self.poly(s, k, (228, 232, 238), outer + inner)
        self.line(s, k, (150, 155, 160), (37, 50), (68, 50), 2)
        self.line(s, k, (150, 155, 160), (47, 24), (68, 50), 0.8)
        self.line(s, k, (150, 155, 160), (47, 76), (68, 50), 0.8)
        self.circ(s, k, (215, 45, 45), 68, 50, 3)

    def draw_launcher(self, s, k, c, v):
        self.box(s, k, (94, 104, 78), 26, 34, 46, 32)
        self.box(s, k, c, 28, 34, 5, 32, False)
        for i in range(4):
            y = 36.5 + i * 7.3
            self.box(s, k, (66, 74, 56), 36, y, 36, 5, False)
            self.poly(s, k, (240, 240, 240), [(72, y), (78, y), (82, y + 2.5), (78, y + 5), (72, y + 5)], False)
            self.poly(s, k, (215, 45, 45), [(78, y), (82, y + 2.5), (78, y + 5)], False)
        pygame.draw.rect(s, OUT, self.R(k, 26, 34, 46, 32), self.W(k, 1.2))

    # ---- Port: pier, crane, containers, docked ship ----
    def draw_port(self, s, k, c, v):
        pygame.draw.ellipse(s, (255, 255, 255, 50), self.R(k, 0, 80, 100, 16))
        for x in (8, 24, 40, 56, 72):
            self.box(s, k, (80, 55, 30), x, 70, 4, 20, False)
        self.box(s, k, (166, 116, 70), 2, 62, 80, 10)
        for x in range(8, 82, 6):
            self.line(s, k, (120, 80, 45), (x, 62), (x, 72), 0.7)
        # containers
        for (x, y, col) in ((5, 48, c), (24, 48, (200, 70, 50)), (14, 34, (60, 150, 95))):
            self.box(s, k, col, x, y, 18, 14)
            for xx in range(int(x) + 3, int(x) + 18, 3):
                self.line(s, k, darker(col, 0.75), (xx, y + 1), (xx, y + 13), 0.6)
        # crane
        yel = (246, 192, 42)
        self.line(s, k, yel, (56, 62), (61, 8), 2.6)
        self.line(s, k, yel, (70, 62), (65, 8), 2.6)
        for y in range(14, 60, 9):
            self.line(s, k, (210, 160, 30), (57 + (62 - y) / 11, y), (69 - (62 - y) / 11, y + 8), 0.8)
        self.line(s, k, yel, (28, 9), (96, 9), 3)
        self.box(s, k, (110, 110, 115), 88, 10, 8, 8)
        self.box(s, k, c, 57, 11, 11, 8)
        self.line(s, k, (50, 50, 50), (36, 10), (36, 28), 0.8)
        self.box(s, k, (232, 160, 60), 30, 28, 13, 8)
        # docked ship
        self.poly(s, k, (150, 42, 42), [(66, 78), (99, 78), (95, 93), (70, 93)])
        self.line(s, k, c, (68, 83), (97, 83), 2)
        self.box(s, k, (240, 240, 240), 86, 69, 9, 9)
        self.box(s, k, (60, 120, 200), 74, 72, 10, 6)

    # ---- Station: brick hall, clock tower, platform, tracks ----
    def draw_station(self, s, k, c, v):
        for x in range(1, 99, 6):
            self.box(s, k, (110, 78, 48), x, 89, 3, 9, False)
        self.line(s, k, (175, 175, 180), (0, 91.5), (100, 91.5), 1.4)
        self.line(s, k, (175, 175, 180), (0, 95.5), (100, 95.5), 1.4)
        self.box(s, k, (192, 192, 194), 2, 76, 96, 10)
        self.line(s, k, (245, 205, 40), (2, 85), (98, 85), 1.2)
        self.box(s, k, (180, 94, 68), 16, 38, 68, 38, False)
        for i, y in enumerate(range(42, 76, 5)):
            self.line(s, k, (150, 74, 52), (16, y), (84, y), 0.5)
        pygame.draw.rect(s, OUT, self.R(k, 16, 38, 68, 38), self.W(k, 1.2))
        for x in (21, 33, 59, 71):
            self.circ(s, k, (252, 232, 172), x + 4, 50, 4)
            self.box(s, k, (252, 232, 172), x, 50, 8, 12, False)
        self.box(s, k, (100, 66, 40), 44, 56, 12, 20)
        self.poly(s, k, c, [(12, 38), (88, 38), (80, 30), (20, 30)])
        self.box(s, k, (192, 106, 78), 42, 12, 16, 22)
        self.poly(s, k, darker(c, 0.8), [(40, 12), (50, 0), (60, 12)])
        self.circ(s, k, (250, 250, 250), 50, 22, 5.5)
        self.circ(s, k, OUT, 50, 22, 5.5, 1)
        self.line(s, k, OUT, (50, 22), (50, 18), 1)
        self.line(s, k, OUT, (50, 22), (53, 23), 1)
        self.poly(s, k, darker(c, 0.6), [(2, 64), (98, 64), (98, 69), (2, 69)])
        for x in (7, 50, 93):
            self.line(s, k, (110, 110, 115), (x, 69), (x, 76), 1.4)


    # ---- Airport: runway, hangar, terminal, control tower ----
    def draw_airport(self, s, k, c, v):
        self.shadow(s, k, 2, 86, 96, 10)
        self.box(s, k, (72, 74, 80), 2, 74, 96, 14)
        for x in range(8, 94, 12):
            self.box(s, k, (240, 240, 240), x, 80, 7, 2, False)
        self.line(s, k, (245, 205, 40), (2, 75), (98, 75), 1)
        self.line(s, k, (245, 205, 40), (2, 87), (98, 87), 1)
        # hangar with curved roof
        self.box(s, k, (186, 191, 199), 4, 50, 34, 22)
        roof = [(4 + 34 * i / 12, 50 - 11 * math.sin(math.pi * i / 12)) for i in range(13)]
        self.poly(s, k, (156, 163, 174), roof + [(38, 50), (4, 50)])
        self.box(s, k, (72, 76, 84), 10, 58, 22, 14)
        for x in range(13, 32, 4):
            self.line(s, k, (110, 114, 122), (x, 58), (x, 72), 0.6)
        self.box(s, k, c, 4, 51, 34, 3, False)
        # terminal
        self.box(s, k, (226, 229, 233), 44, 54, 52, 18)
        self.box(s, k, (118, 168, 214), 46, 58, 48, 5, False)
        self.box(s, k, c, 44, 52, 52, 3)
        # control tower
        self.box(s, k, (236, 236, 239), 63, 18, 8, 36)
        self.poly(s, k, (110, 170, 222), [(58, 10), (76, 10), (78, 18), (56, 18)])
        self.box(s, k, c, 58, 6, 18, 4)
        self.line(s, k, (70, 70, 70), (67, 6), (67, 0), 0.8)
        self.circ(s, k, (235, 50, 50), 67, 1, 1.5)
        # parked plane on the runway
        self.poly(s, k, (250, 250, 250), [(50, 81), (74, 79.5), (78, 81), (74, 82.5), (50, 82.5)])
        self.poly(s, k, (230, 232, 236), [(64, 80), (60, 73), (57, 73), (59, 80)])
        self.poly(s, k, (230, 232, 236), [(64, 82), (60, 89), (57, 89), (59, 82)])
        self.poly(s, k, c, [(51, 81), (48, 76), (46, 76), (48, 81.5)])


class Renderer:
    def __init__(self, screen):
        self.screen = screen
        self.view = screen.subsurface((0, 0, MAP_W, MAP_H))
        self.overlay = pygame.Surface((MAP_W, MAP_H), pygame.SRCALPHA)
        self.fonts = {}
        self.sprites = Sprites()
        self.mips = []
        self.base_key = None
        self.base_img = None
        path = asset_path(TEXTURE_FILE)
        if path:
            try:
                tex = pygame.image.load(path).convert()
                self.mips = [tex]
                while self.mips[-1].get_width() > 1400:
                    m = self.mips[-1]
                    self.mips.append(pygame.transform.smoothscale(m, (m.get_width() // 2, m.get_height() // 2)))
            except Exception as exc:
                print("Could not load", path, exc)
                self.mips = []
        self.cam = Camera()
        self.buttons = [pygame.Rect(452 + i * 68, MAP_H + 22, 64, 58) for i in range(len(MODES))]
        self.menu = None
        self.menu_rects = []
        self.popup_rects = []
        self.slider = pygame.Rect(236, MAP_H + 52, 190, 8)

    def font(self, size, bold=False):
        key = (size, bold)
        if key not in self.fonts:
            self.fonts[key] = pygame.font.SysFont("arial", size, bold=bold)
        return self.fonts[key]

    def text(self, surf, s, pos, size=14, color=(255, 255, 255), bold=False, center=False, shadow=False):
        f = self.font(int(size), bold)
        img = f.render(s, True, color)
        r = img.get_rect()
        if center:
            r.center = (int(pos[0]), int(pos[1]))
        else:
            r.topleft = (int(pos[0]), int(pos[1]))
        if shadow:
            surf.blit(f.render(s, True, (0, 0, 0)), r.move(1, 1))
        surf.blit(img, r)

    # sizes that grow gently with zoom
    def icon_size(self):
        return ICON_BASE * (0.6 + 0.4 * self.cam.z)

    def unit(self):
        return 0.9 + 0.35 * self.cam.z

    def visible(self, sx, sy, margin=80):
        return -margin <= sx <= MAP_W + margin and -margin <= sy <= MAP_H + margin

    def mouse_tile(self, mouse):
        wx, wy = self.cam.s2w(*mouse)
        return int(wx // TS), int(wy // TS)

    # --- map ---
    def draw_map(self, g):
        cam, v = self.cam, self.view
        tx0, ty0 = int(cam.ox // TS), int(cam.oy // TS)
        tx1 = min(GW, int((cam.ox + MAP_W / cam.z) // TS) + 2)
        ty1 = min(GH, int((cam.oy + MAP_H / cam.z) // TS) + 2)
        tx0, ty0 = min(tx0, GW - 1), min(ty0, GH - 1)
        w = round((tx1 - tx0) * TS * cam.z)
        h = round((ty1 - ty0) * TS * cam.z)
        sx, sy = cam.w2s(tx0 * TS, ty0 * TS)
        pos = (round(sx), round(sy))
        tiles = (tx0, ty0, tx1 - tx0, ty1 - ty0)
        if self.mips and g.base is None:
            key = (tx0, ty0, tx1, ty1, w, h)
            if key != self.base_key:
                need = GW * TS * cam.z
                tex = self.mips[0]
                for m in self.mips:
                    if m.get_width() >= need:
                        tex = m
                k = tex.get_width() / GW
                rect = pygame.Rect(round(tx0 * k), round(ty0 * k), max(1, round((tx1 - tx0) * k)),
                                   max(1, round((ty1 - ty0) * k))).clip(tex.get_rect())
                self.base_img = pygame.transform.smoothscale(tex.subsurface(rect), (w, h))
                self.base_key = key
            v.blit(self.base_img, pos)
        elif g.base is not None:
            v.blit(pygame.transform.scale(g.base.subsurface(tiles), (w, h)), pos)
        v.blit(pygame.transform.scale(g.terr.subsurface(tiles), (w, h)), pos)

    # --- buildings ---
    def draw_building(self, g, b, p, t):
        sx, sy = self.cam.w2s(*b.pos)
        if not self.visible(sx, sy):
            return
        size = self.icon_size()
        if b.kind == "silo":
            spr = self.sprites.get("silo", p.color, size, 1 if b.cooldown <= 0 else 0)
        else:
            spr = self.sprites.get(b.kind, p.color, size)
        x0, y0 = sx - spr.get_width() / 2, sy - spr.get_height() * 0.72
        self.view.blit(spr, (x0, y0))
        sz = spr.get_width()
        if b.kind == "airdef":
            deg = -math.degrees(b.angle)
            launcher = self.sprites.get("launcher", p.color, sz * 0.55)
            lr = pygame.transform.rotozoom(launcher, deg, 1.0)
            self.view.blit(lr, lr.get_rect(center=(x0 + sz * 0.5, y0 + sz * 0.6)))
            dish = self.sprites.get("dish", p.color, sz * (0.62 + 0.04 * b.level))
            dr = pygame.transform.rotozoom(dish, deg, 1.0)
            self.view.blit(dr, dr.get_rect(center=(x0 + sz * 0.5, y0 + sz * 0.28)))
            on = b.tracking or int(t * 3) % 2 == 0
            pygame.draw.circle(self.view, (255, 60, 60) if on else (110, 30, 30),
                               (int(x0 + sz * 0.5), int(y0 + sz * 0.62)), max(2, int(sz * 0.04)))
        if b.level > 1 or b.kind == "airdef":
            r = max(2.5, sz * 0.055)
            total = b.level * r * 2.1
            for i in range(b.level):
                cx = x0 + sz / 2 - total / 2 + r + i * r * 2.1
                cy = y0 + sz + r * 0.6
                pts = star_points(cx, cy, r)
                pygame.draw.polygon(self.view, (255, 210, 60), pts)
                pygame.draw.polygon(self.view, (90, 60, 0), pts, 1)
        if b.kind == "silo" and b.cooldown > 0:
            frac = 1 - b.cooldown / max(0.1, b.cd_total)
            rr = pygame.Rect(0, 0, sz * 0.7, sz * 0.7)
            rr.center = (x0 + sz / 2, y0 + sz * 0.55)
            pygame.draw.arc(self.view, (255, 220, 80), rr, math.pi / 2, math.pi / 2 + frac * math.tau, 3)

    def draw_track(self, pts, col, tie_col=(96, 70, 44)):
        """Rails with evenly spaced sleepers along a list of screen points."""
        v = self.view
        u = self.unit()
        half = 2.6 * u
        step = 4.5 * u
        carry = 0.0
        for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
            L = math.dist((x0, y0), (x1, y1))
            if L < 0.5:
                continue
            ux, uy = (x1 - x0) / L, (y1 - y0) / L
            nx, ny = -uy, ux
            dd = carry
            while dd < L:
                px, py = x0 + ux * dd, y0 + uy * dd
                pygame.draw.line(v, tie_col, (px - nx * half, py - ny * half),
                                 (px + nx * half, py + ny * half), max(2, int(u * 1.1)))
                dd += step
            carry = dd - L
        for side in (-0.55, 0.55):
            off = []
            for i, (x, y) in enumerate(pts):
                a = pts[max(0, i - 1)]
                b = pts[min(len(pts) - 1, i + 1)]
                L = math.dist(a, b) or 1
                nx, ny = -(b[1] - a[1]) / L, (b[0] - a[0]) / L
                off.append((x + nx * half * side, y + ny * half * side))
            pygame.draw.lines(v, col, False, off, max(1, int(u * 0.8)))

    def draw_rails(self, g):
        cam = self.cam
        joints = {}
        for e in g.rails:
            pts = [cam.w2s(*q) for q in e.pts]
            xs = [q[0] for q in pts]
            ys = [q[1] for q in pts]
            if max(xs) < -20 or min(xs) > MAP_W + 20 or max(ys) < -20 or min(ys) > MAP_H + 20:
                continue
            foreign = g.owner_of(e.a) != g.owner_of(e.b)
            self.draw_track(pts, (240, 200, 70) if foreign else (198, 198, 204))
            for q in (pts[0], pts[-1]):
                key = (int(q[0]), int(q[1]))
                joints[key] = joints.get(key, 0) + 1
        r = max(2, int(2.2 * self.unit()))
        for (x, y), n in joints.items():
            if n >= 2:
                pygame.draw.circle(self.view, (60, 60, 66), (x, y), r + 1)
                pygame.draw.circle(self.view, (210, 210, 216), (x, y), r)

    def draw_train(self, g, tr, p, t):
        """Diesel locomotive pulling black oil-tanker wagons."""
        u = self.unit()
        v = self.view
        cars = []
        for kidx in range(4):
            (wx, wy), ang = tr.point(back=kidx * 15 * u / self.cam.z)
            x, y = self.cam.w2s(wx, wy)
            cars.append((x, y, ang))
        if not any(self.visible(x, y) for x, y, _ in cars):
            return
        for kidx in range(3, -1, -1):
            x, y, ang = cars[kidx]
            if kidx == 0:
                body = rot(x, y, ang, [(-7, -3.2), (6, -3.2), (7.5, -1.5), (7.5, 1.5), (6, 3.2), (-7, 3.2)], u)
                pygame.draw.polygon(v, (48, 50, 56), body)
                pygame.draw.polygon(v, p.color, rot(x, y, ang, [(-7, -3.2), (-2, -3.2), (-2, 3.2), (-7, 3.2)], u))
                pygame.draw.polygon(v, (245, 200, 40), rot(x, y, ang, [(3, -3.2), (4, -3.2), (4, 3.2), (3, 3.2)], u))
                pygame.draw.polygon(v, OUT, body, 1)
                fx, fy = rot(x, y, ang, [(7.2, 0)], u)[0]
                pygame.draw.circle(v, (255, 238, 150), (int(fx), int(fy)), max(1, int(1.2 * u)))
            else:
                end1, end2 = rot(x, y, ang, [(-5.5, 0), (5.5, 0)], u)
                tank = rot(x, y, ang, [(-5.5, -3.2), (5.5, -3.2), (5.5, 3.2), (-5.5, 3.2)], u)
                pygame.draw.polygon(v, (34, 34, 38), tank)
                for ex, ey in (end1, end2):
                    pygame.draw.circle(v, (34, 34, 38), (int(ex), int(ey)), max(1, int(3.2 * u)))
                hl = rot(x, y, ang, [(-6, -1.6), (6, -1.6)], u)
                pygame.draw.line(v, (120, 122, 132), hl[0], hl[1], max(1, int(u)))
                pygame.draw.polygon(v, p.color, rot(x, y, ang, [(-1, -3.2), (1, -3.2), (1, 3.2), (-1, 3.2)], u))
                dx, dy = rot(x, y, ang, [(2.8, 0)], u)[0]
                pygame.draw.circle(v, (150, 152, 158), (int(dx), int(dy)), max(1, int(1.2 * u)))
        x, y, ang = cars[0]
        for i in range(4):
            ph = (t * 2 + i / 4) % 1
            bx, by = rot(x, y, ang, [(1 - ph * 12, 0)], u)[0]
            pygame.draw.circle(self.overlay, (210, 210, 210, int(150 * (1 - ph))),
                               (int(bx), int(by - ph * 8 * u)), max(1, int((1.3 + ph * 3) * u)))

    def draw_plane(self, g, pl, shadow_only=False):
        wx, wy = pl.pos()
        x, y = self.cam.w2s(wx, wy)
        if not self.visible(x, y):
            return
        t = pl.t()
        alt = math.sin(math.pi * t)
        u = self.unit() * (1.1 + 0.5 * alt)
        a = pl.heading
        col = g.players[pl.captured_by if pl.captured_by is not None else pl.owner].color
        body = [(10, 0), (8, -1.6), (-8, -1.6), (-10.5, 0), (-8, 1.6), (8, 1.6)]
        wing1 = [(2, -1.5), (-3, -10), (-5.5, -10), (-2.5, -1.5)]
        wing2 = [(2, 1.5), (-3, 10), (-5.5, 10), (-2.5, 1.5)]
        tail1 = [(-7, -1.5), (-10, -4.5), (-11.5, -4.5), (-10, -1.5)]
        tail2 = [(-7, 1.5), (-10, 4.5), (-11.5, 4.5), (-10, 1.5)]
        if shadow_only:
            sx, sy = x + 6 + 18 * alt * u, y + 8 + 22 * alt * u
            for part in (body, wing1, wing2):
                pygame.draw.polygon(self.overlay, (0, 0, 0, 70), rot(sx, sy, a, part, self.unit()))
            return
        for part in (wing1, wing2, tail1, tail2):
            pygame.draw.polygon(self.view, (225, 228, 234), rot(x, y, a, part, u))
            pygame.draw.polygon(self.view, OUT, rot(x, y, a, part, u), 1)
        pygame.draw.polygon(self.view, (250, 250, 252), rot(x, y, a, body, u))
        pygame.draw.polygon(self.view, OUT, rot(x, y, a, body, u), 1)
        pygame.draw.polygon(self.view, col, rot(x, y, a, [(-7, -1.6), (-10.5, -0.4), (-10.5, 0.4), (-7, 1.6)], u))
        pygame.draw.polygon(self.view, col, rot(x, y, a, [(4, -1.6), (6, -1.6), (6, 1.6), (4, 1.6)], u))

    def draw_warship(self, g, w, t):
        x, y = self.cam.w2s(w.x, w.y)
        if not self.visible(x, y):
            return
        p = g.players[w.owner]
        u = self.unit() * 1.1
        a = w.heading
        for side in (-1, 1):
            pts = rot(x, y, a, [(-14, side * 5), (-28, side * 11)], u)
            pygame.draw.line(self.overlay, (235, 245, 255, 120), pts[0], pts[1], max(1, int(u)))
        hull = [(17, 0), (12, -5.5), (-13, -5.5), (-15, -3), (-15, 3), (-13, 5.5), (12, 5.5)]
        pygame.draw.polygon(self.view, (116, 124, 136), rot(x, y, a, hull, u))
        pygame.draw.polygon(self.view, p.color, rot(x, y, a, [(12, -5.5), (-13, -5.5), (-13, -4), (12, -4)], u))
        pygame.draw.polygon(self.view, p.color, rot(x, y, a, [(12, 5.5), (-13, 5.5), (-13, 4), (12, 4)], u))
        pygame.draw.polygon(self.view, OUT, rot(x, y, a, hull, u), 1)
        pygame.draw.polygon(self.view, (164, 172, 182), rot(x, y, a, [(3, -3), (-6, -3), (-6, 3), (3, 3)], u))
        pygame.draw.polygon(self.view, (60, 80, 110), rot(x, y, a, [(2, -2), (0, -2), (0, 2), (2, 2)], u))
        aim = math.atan2(w.firing[1] - w.y, w.firing[0] - w.x) if w.firing else a
        for tx_ in (9, -10):
            cx, cy = rot(x, y, a, [(tx_, 0)], u)[0]
            pygame.draw.circle(self.view, (88, 94, 104), (int(cx), int(cy)), max(2, int(2.6 * u)))
            pygame.draw.line(self.view, (60, 64, 72), (cx, cy),
                             (cx + math.cos(aim) * 7 * u, cy + math.sin(aim) * 7 * u), max(1, int(1.2 * u)))
        if w.firing:
            fx, fy = self.cam.w2s(*w.firing)
            if int(t * 12) % 2 == 0:
                pygame.draw.line(self.view, (255, 230, 120), (x, y), (fx, fy), 1)
                pygame.draw.circle(self.view, (255, 200, 80), (int(fx), int(fy)), max(2, int(3 * u)))
        if w.hp < WARSHIP_HP:
            bw = 26 * u
            pygame.draw.rect(self.view, (40, 0, 0), (x - bw / 2, y - 12 * u, bw, 3))
            pygame.draw.rect(self.view, (90, 230, 90), (x - bw / 2, y - 12 * u, bw * max(0, w.hp) / WARSHIP_HP, 3))

    def draw_jet(self, g, j, t):
        x, y = self.cam.w2s(j.x, j.y)
        pts = [self.cam.w2s(*q) for q in j.trail]
        for i in range(1, len(pts)):
            pygame.draw.line(self.overlay, (255, 255, 255, 12 + i * 8), pts[i - 1], pts[i], max(1, int(self.unit())))
        if not self.visible(x, y):
            return
        p = g.players[j.owner]
        u = self.unit() * 0.95
        a = j.heading
        body = [(14, 0), (6, -2), (-2, -2.5), (-10, -2), (-12, -1.5), (-12, 1.5), (-10, 2), (-2, 2.5), (6, 2)]
        wing1 = [(4, -2), (-6, -10), (-9, -10), (-5, -2)]
        wing2 = [(4, 2), (-6, 10), (-9, 10), (-5, 2)]
        fin1 = [(-8, -2), (-12, -6), (-13.5, -6), (-12, -1.5)]
        fin2 = [(-8, 2), (-12, 6), (-13.5, 6), (-12, 1.5)]
        for part in (wing1, wing2, fin1, fin2):
            pygame.draw.polygon(self.view, (78, 86, 100), rot(x, y, a, part, u))
            pygame.draw.polygon(self.view, OUT, rot(x, y, a, part, u), 1)
        pygame.draw.polygon(self.view, p.color, rot(x, y, a, [(-1, -6), (-6, -9), (-7, -8), (-3, -4)], u))
        pygame.draw.polygon(self.view, p.color, rot(x, y, a, [(-1, 6), (-6, 9), (-7, 8), (-3, 4)], u))
        pygame.draw.polygon(self.view, (96, 104, 118), rot(x, y, a, body, u))
        pygame.draw.polygon(self.view, OUT, rot(x, y, a, body, u), 1)
        pygame.draw.polygon(self.view, (120, 200, 255), rot(x, y, a, [(8, -1), (4, -1.4), (4, 1.4), (8, 1)], u))
        fl = 3 + 3 * random.random()
        f = rot(x, y, a, [(-12, -1), (-12 - fl, 0), (-12, 1)], u)
        pygame.draw.polygon(self.view, (255, 170, 50), f)

    def building_tile(self, mouse):
        """Tile under a building icon (icons are drawn above their tile)."""
        tx, ty = self.mouse_tile(mouse)
        return tx, ty + round(self.icon_size() * 0.22 / (TS * self.cam.z))

    # --- right-click menu & alliance popup ---
    def open_menu(self, g, pos):
        tx, ty = self.mouse_tile(pos)
        if not (0 <= tx < GW and 0 <= ty < GH) or not g.land[ty][tx]:
            return
        o = g.owner[ty][tx]
        if o == 0:
            return
        opts = []
        ally = o >= 0 and g.is_ally(0, o)
        if not ally:
            if g.borders(0, o):
                opts.append(("Attack", "attack", (255, 120, 110)))
            opts.append(("Send boat", "boat", (130, 190, 255)))
        if o >= 0 and not g.players[o].tribe:
            if ally:
                opts.append(("Betray alliance", "betray", (255, 160, 60)))
            else:
                opts.append(("Request alliance", "ally", (130, 240, 150)))
        title = ("Neutral land" if o < 0 else g.players[o].name + ("  (ally)" if ally else "")
                 + (f"  - gold {fmt(g.players[o].gold)}" if o >= 0 and g.players[o].tribe else ""))
        self.menu = {"pos": pos, "tile": (tx, ty), "owner": o, "title": title, "opts": opts}

    def menu_click(self, g, pos):
        m = self.menu
        for rect, action in self.menu_rects:
            if rect.collidepoint(pos):
                tx, ty = m["tile"]
                o = m["owner"]
                err = None
                if action == "attack":
                    err = g.send_attack(0, o, g.ratio)
                elif action == "boat":
                    err = g.send_boat(0, tx, ty, g.ratio)
                elif action == "ally":
                    err = g.request_alliance(0, o)
                elif action == "betray":
                    m["opts"] = [(f"Yes, betray {g.players[o].name}", "betray_yes", (255, 90, 70)),
                                 ("Cancel", "cancel", (200, 200, 210))]
                    m["title"] = "Are you sure?"
                    return
                elif action == "betray_yes":
                    err = g.betray(0, o)
                    if not err and g.borders(0, o):
                        g.msg("Left-click their land to attack", (200, 200, 210))
                if err:
                    g.msg(err, (255, 160, 160))
                break
        self.menu = None

    def draw_menu(self, g):
        self.menu_rects = []
        m = self.menu
        if not m:
            return
        w, rh = 190, 28
        h = 30 + rh * len(m["opts"])
        x, y = m["pos"]
        x = min(x + 8, WIN_W - w - 4)
        y = min(y + 8, WIN_H - h - 4)
        box = pygame.Surface((w, h), pygame.SRCALPHA)
        box.fill((20, 24, 34, 235))
        self.screen.blit(box, (x, y))
        pygame.draw.rect(self.screen, (90, 100, 130), (x, y, w, h), 2, border_radius=4)
        self.text(self.screen, m["title"], (x + 10, y + 7), 13, (255, 255, 255), True)
        mouse = pygame.mouse.get_pos()
        for i, (label, action, col) in enumerate(m["opts"]):
            r = pygame.Rect(x + 4, y + 28 + i * rh, w - 8, rh - 2)
            if r.collidepoint(mouse):
                pygame.draw.rect(self.screen, (55, 64, 88), r, border_radius=4)
            pygame.draw.circle(self.screen, col, (r.x + 12, r.centery), 5)
            self.text(self.screen, label, (r.x + 24, r.y + 5), 14, col, True)
            self.menu_rects.append((r, action))

    def draw_popup(self, g):
        self.popup_rects = []
        if not g.incoming or g.phase != "play":
            return
        req = g.incoming[0]
        other = g.players[req["frm"]]
        w, h = 420, 82
        x, y = (MAP_W - w) // 2, 60
        box = pygame.Surface((w, h), pygame.SRCALPHA)
        box.fill((20, 26, 38, 240))
        self.screen.blit(box, (x, y))
        pygame.draw.rect(self.screen, other.color, (x, y, w, h), 3, border_radius=6)
        secs = max(0, int(req["expires"] - g.time))
        self.text(self.screen, f"{other.name} proposes an alliance  ({secs}s)", (x + w // 2, y + 18), 16,
                  (255, 255, 255), True, True)
        acc = pygame.Rect(x + 60, y + 38, 130, 32)
        rej = pygame.Rect(x + w - 190, y + 38, 130, 32)
        mouse = pygame.mouse.get_pos()
        for r, label, col in ((acc, "Accept", (60, 170, 90)), (rej, "Reject", (190, 70, 70))):
            pygame.draw.rect(self.screen, lighter(col, 0.2) if r.collidepoint(mouse) else col, r, border_radius=6)
            self.text(self.screen, label, r.center, 15, (255, 255, 255), True, True)
        self.popup_rects = [(acc, True), (rej, False)]

    def draw_station_preview(self, g, mouse):
        """Show the exact tracks a station placed here would build."""
        tx, ty = self.mouse_tile(mouse)
        if not (0 <= tx < GW and 0 <= ty < GH):
            return
        v, o, cam = self.view, self.overlay, self.cam
        mx, my = mouse
        pygame.draw.circle(o, (255, 220, 150, 45), (mx, my), RAIL_RANGE * TS * cam.z, 2)
        err = g.can_build(0, "station", tx, ty)
        fake = Building("station", tx, ty)
        own = foreign = 0
        if not err:
            key = (tx, ty, len(g.buildings), int(g.time))
            if getattr(self, "preview_key", None) != key:
                mine = [b for b in g.buildings if g.owner_of(b) == 0]
                stations = [b for b in mine if b.kind == "station"]
                hubs = [b for b in mine if b.kind in ("city", "port", "airport")]
                others = [b for b in g.buildings if b.kind == "station" and g.owner_of(b) not in (-1, 0)]
                self.preview_links = g.plan_links(fake, 0, stations, hubs, others, cache=False)
                self.preview_key = key
            for b, tiles in self.preview_links:
                bx, by = cam.w2s(*b.pos)
                if tiles:
                    is_foreign = g.owner_of(b) != 0
                    col = (255, 210, 60) if is_foreign else (90, 255, 130)
                    foreign += is_foreign
                    own += not is_foreign
                    self.draw_track([cam.w2s(*q) for q in corner_points(tiles)], col, (60, 90, 60))
                else:
                    pygame.draw.line(v, (255, 80, 80), (mx, my), (bx, by), 1)
                    col = (255, 80, 80)
                pygame.draw.circle(v, col, (int(bx), int(by)), 7, 2)
        if err:
            info, col = err, (255, 120, 120)
        elif own + foreign == 0:
            info, col = "Station: nothing to connect to here yet", (255, 210, 150)
        else:
            parts = [f"connects to {own} of your buildings"]
            if foreign:
                parts.append(f"{foreign} foreign station - train trade")
            info, col = "Station: " + ", ".join(parts), (180, 255, 190)
        self.text(v, info, (mx + 16, my + 12), 13, col, True, False, True)

    def draw_boat(self, g, bt):
        wx, wy = bt.pos()
        x, y = self.cam.w2s(wx, wy)
        if not self.visible(x, y):
            return
        p = g.players[bt.owner]
        a, u = bt.heading, self.unit()
        # wake
        for side in (-1, 1):
            pts = rot(x, y, a, [(-10, side * 4), (-22, side * 9)], u)
            pygame.draw.line(self.overlay, (235, 245, 255, 110), pts[0], pts[1], max(1, int(u)))
        if bt.kind == "transport":
            hull = rot(x, y, a, [(12, 0), (7, -5), (-10, -5), (-11, 0), (-10, 5), (7, 5)], u)
            pygame.draw.polygon(self.view, p.color, hull)
            pygame.draw.polygon(self.view, OUT, hull, 1)
            pygame.draw.polygon(self.view, (238, 238, 238), rot(x, y, a, [(5, -3), (-6, -3), (-6, 3), (5, 3)], u))
            pygame.draw.polygon(self.view, (120, 125, 135), rot(x, y, a, [(-3, -2), (-8, -2), (-8, 2), (-3, 2)], u))
            for i in range(3):
                hx, hy = rot(x, y, a, [(3 - i * 3, 0)], u)[0]
                pygame.draw.circle(self.view, darker(p.color, 0.6), (int(hx), int(hy)), max(1, int(1.1 * u)))
            self.text(self.view, fmt(bt.troops), (x, y - 12 * u), 10 + 2 * self.cam.z, (255, 255, 255), True, True, True)
        else:
            hull = rot(x, y, a, [(14, 0), (9, -5.5), (-13, -5.5), (-13, 5.5), (9, 5.5)], u)
            pygame.draw.polygon(self.view, (135, 50, 45), hull)
            pygame.draw.polygon(self.view, OUT, hull, 1)
            ob = g.owner_of(bt.dst)
            other = g.players[ob].color if ob >= 0 else p.color
            cols = [p.color, other, (230, 160, 60), (60, 150, 95)]
            for i in range(4):
                xx = 7 - i * 5
                pygame.draw.polygon(self.view, cols[i], rot(x, y, a, [(xx, -4), (xx - 4.5, -4), (xx - 4.5, 4), (xx, 4)], u))
            pygame.draw.polygon(self.view, (245, 245, 245), rot(x, y, a, [(-12, -3), (-9, -3), (-9, 3), (-12, 3)], u))

    # --- main draw ---
    def draw(self, g, mouse):
        s, v, o, cam = self.screen, self.view, self.overlay, self.cam
        t = pygame.time.get_ticks() / 1000
        z = cam.z
        s.fill((12, 22, 48))
        self.draw_map(g)
        o.fill((0, 0, 0, 0))

        def W(pt):
            return cam.w2s(pt[0], pt[1])

        for b in g.buildings:
            ow = g.owner_of(b)
            if b.kind == "airdef" and ow >= 0:
                col = g.players[ow].color
                cx, cy = W(b.pos)
                R = b.range * TS * z
                pygame.draw.circle(o, (*col, 24), (cx, cy), R)
                pygame.draw.circle(o, (*col, 120 if b.tracking else 70), (cx, cy), R, 2 if b.tracking else 1)
                for ring in range(1, b.level):
                    rr = (AD_BASE_RANGE + AD_RANGE_STEP * (ring - 1)) * TS * z
                    pygame.draw.circle(o, (*col, 25), (cx, cy), rr, 1)
                for i in range(10):
                    a = b.sweep - i * 0.05
                    pygame.draw.line(o, (*col, max(0, 140 - i * 14)), (cx, cy),
                                     (cx + math.cos(a) * R, cy + math.sin(a) * R), 2)

        for nk in g.nukes:
            for i, pt in enumerate(nk.trail):
                x, y = W(pt)
                pygame.draw.circle(o, (200, 200, 200, int(10 + i * 3)), (int(x), int(y)), int((2 + i // 15) * self.unit()))
            pulse = 0.5 + 0.5 * math.sin(t * 8)
            pygame.draw.circle(o, (255, 40, 40, int(40 + 50 * pulse)), W(nk.end), NUKE_RADIUS * TS * z, 2)
        for it in g.interceptors:
            for i, pt in enumerate(it.trail):
                x, y = W(pt)
                pygame.draw.circle(o, (180, 255, 255, 30 + i * 14), (int(x), int(y)), int(3 * self.unit()))

        for e in g.effects:
            k = e["t"] / e["dur"]
            x, y = W(e["pos"])
            if e["kind"] == "boom":
                rr = NUKE_RADIUS * TS * z * (0.3 + 0.9 * k)
                pygame.draw.circle(o, (255, 150, 40, int(200 * (1 - k))), (x, y), rr)
                pygame.draw.circle(o, (255, 255, 200, int(255 * (1 - k))), (x, y), rr * 0.5)
                pygame.draw.circle(o, (255, 255, 255, int(180 * (1 - k))), (x, y), rr * 1.2, 3)
            elif e["kind"] == "intercept":
                rr = (6 + 22 * k) * self.unit()
                pygame.draw.circle(o, (255, 240, 150, int(230 * (1 - k))), (x, y), rr)
                pygame.draw.circle(o, (255, 255, 255, int(255 * (1 - k))), (x, y), rr + 4, 2)
            elif e["kind"] == "ring":
                pygame.draw.circle(o, (140, 255, 200, int(220 * (1 - k))), (x, y), e["r"] * z * (0.6 + 0.4 * k), 3)
            elif e["kind"] == "sink":
                rr = (5 + 18 * k) * self.unit()
                pygame.draw.circle(o, (255, 170, 60, int(220 * (1 - k))), (x, y), rr * 0.6)
                pygame.draw.circle(o, (90, 90, 90, int(160 * (1 - k))), (x, y - 6 * k * self.unit()), rr)
            elif e["kind"] == "puff":
                pygame.draw.circle(o, (170, 170, 170, int(160 * (1 - k))), (x, y), (4 + 8 * k) * self.unit())

        mx, my = mouse
        in_map = my < MAP_H
        if g.mode and in_map and g.phase == "play":
            if g.mode == "nuke":
                pygame.draw.circle(o, (255, 40, 40, 60), (mx, my), NUKE_RADIUS * TS * z)
                pygame.draw.circle(o, (255, 40, 40, 200), (mx, my), NUKE_RADIUS * TS * z, 2)
            elif g.mode == "airdef":
                pygame.draw.circle(o, (*g.players[0].color, 40), (mx, my), AD_BASE_RANGE * TS * z)
            elif g.mode == "defense":
                pygame.draw.circle(o, (255, 255, 255, 40), (mx, my), DEFENSE_RANGE * TS * z)
            elif g.mode == "upgrade":
                b = g.building_near(0, *self.building_tile(mouse))
                if b and b.kind == "airdef" and b.level < MAX_LEVEL:
                    pygame.draw.circle(o, (140, 255, 200, 160), W(b.pos), (b.range + AD_RANGE_STEP) * TS * z, 2)
                elif b:
                    pygame.draw.circle(o, (140, 255, 200, 160), W(b.pos), self.icon_size() * 0.7, 2)
            elif g.mode == "warship":
                b = g.building_near(0, *self.building_tile(mouse), "port", 10)
                if b:
                    pygame.draw.circle(o, (130, 190, 255, 160), W(b.pos), self.icon_size() * 0.7, 3)
            elif g.mode == "jet":
                b = g.building_near(0, *self.building_tile(mouse), "airport", 10)
                if b:
                    pygame.draw.circle(o, (130, 190, 255, 160), W(b.pos), self.icon_size() * 0.7, 3)
                    pygame.draw.circle(o, (130, 190, 255, 50), W(b.pos), JET_RANGE * TS * z, 1)

        self.draw_rails(g)
        for tr in g.trains:
            self.draw_train(g, tr, g.players[tr.owner], t)
        for bt in g.boats:
            self.draw_boat(g, bt)
        for w in g.warships:
            self.draw_warship(g, w, t)
        for pl in g.planes:
            self.draw_plane(g, pl, shadow_only=True)
        v.blit(o, (0, 0))

        for b in sorted(g.buildings, key=lambda b: b.y):
            ow = g.owner_of(b)
            if ow >= 0:
                self.draw_building(g, b, g.players[ow], t)

        for pl in g.planes:
            self.draw_plane(g, pl)
        self.overlay.fill((0, 0, 0, 0))
        for j in g.jets:
            self.draw_jet(g, j, t)
        if g.jets:
            v.blit(self.overlay, (0, 0))

        if g.mode == "station" and in_map and g.phase == "play":
            self.overlay.fill((0, 0, 0, 0))
            self.draw_station_preview(g, mouse)
            v.blit(self.overlay, (0, 0))

        for p in g.players:
            if p.alive and p.label_pos:
                size = max(10, min(24, 8 + math.sqrt(len(p.tiles) / 30) * 0.35)) * (0.8 + 0.3 * z)
                x, y = W(p.label_pos)
                if self.visible(x, y, 0):
                    ncol = (150, 255, 170) if g.is_ally(0, p.id) else (230, 210, 180) if p.tribe else (255, 255, 255)
                    if p.tribe:
                        size *= 0.8
                    if g.is_traitor(p.id):
                        self.text(v, "TRAITOR", (x, y - size * 1.4), max(10, size * 0.6), (255, 110, 60), True, True, True)
                    self.text(v, p.name, (x, y - size / 2), size, ncol, True, True, True)
                    self.text(v, fmt(p.troops), (x, y + size / 2), size - 2, (255, 240, 180), False, True, True)

        for nk in g.nukes:
            x, y = W(nk.pos)
            u = self.unit()
            body = rot(x, y, nk.heading, [(8, 0), (-5, 3), (-5, -3)], u)
            pygame.draw.polygon(v, (235, 235, 235), body)
            pygame.draw.polygon(v, (200, 30, 30), body, 1)
            fl = 4 + random.random() * 4
            p1 = rot(x, y, nk.heading, [(-5, 0), (-5 - fl, 0)], u)
            pygame.draw.line(v, (255, 170, 40), p1[0], p1[1], max(2, int(2 * u)))
        for it in g.interceptors:
            x, y = W(it.pos)
            pygame.draw.circle(v, (255, 255, 255), (int(x), int(y)), int(3 * self.unit()))
            pygame.draw.circle(v, it.color, (int(x), int(y)), int(3 * self.unit()), 2)

        for e in g.effects:
            if e["kind"] == "coin":
                k = e["t"] / e["dur"]
                x, y = W(e["pos"])
                self.text(v, e["text"], (x, y - 14 - 18 * k), 12 + z, (255, 215, 80), True, True, True)

        if g.mode == "upgrade" and in_map and g.phase == "play":
            b = g.building_near(0, *self.building_tile(mouse))
            if b:
                if b.level >= MAX_LEVEL:
                    tip = f"{LABEL[b.kind]} level {b.level} (max)"
                else:
                    extra = f" ({b.range} -> {b.range + AD_RANGE_STEP})" if b.kind == "airdef" else ""
                    tip = (f"{LABEL[b.kind]} Lv {b.level} -> {b.level + 1}: {fmt(g.upgrade_cost(b))} gold - "
                           f"{UPGRADE_INFO[b.kind]}{extra}")
            else:
                tip = "Click one of your buildings to upgrade it"
            self.text(v, tip, (mx + 14, my - 18), 13, (255, 255, 255), True, False, True)
        elif g.mode == "warship" and in_map and g.phase == "play":
            self.text(v, "Click one of your ports to launch a warship", (mx + 14, my - 18), 13,
                      (200, 230, 255), True, False, True)
        elif g.mode == "jet" and in_map and g.phase == "play":
            self.text(v, "Click one of your airports to launch a fighter jet (captures enemy planes)",
                      (mx + 14, my - 18), 13, (200, 230, 255), True, False, True)

        self.draw_leaderboard(g)
        self.draw_messages(g)
        self.draw_panel(g, mouse)
        self.draw_overlays(g)
        self.draw_popup(g)
        self.draw_menu(g)

    def draw_leaderboard(self, g):
        alive = sorted([p for p in g.players if p.alive and not p.tribe], key=lambda p: -len(p.tiles))
        tribes = sum(1 for p in g.players if p.alive and p.tribe)
        x0 = MAP_W - 238
        box = pygame.Surface((230, 38 + 18 * len(alive)), pygame.SRCALPHA)
        box.fill((0, 0, 0, 150))
        self.screen.blit(box, (x0, 8))
        self.text(self.screen, "Leaderboard", (x0 + 8, 10), 13, (220, 220, 220), True)
        for i, p in enumerate(alive):
            y = 28 + i * 18
            pygame.draw.rect(self.screen, p.color, (x0 + 8, y + 3, 10, 10))
            self.text(self.screen, p.name, (x0 + 23, y), 13)
            if g.is_traitor(p.id):
                self.text(self.screen, "TRAITOR", (x0 + 112, y + 1), 11, (255, 130, 60), True)
            elif p.id != 0 and g.is_ally(0, p.id):
                self.text(self.screen, "ALLY", (x0 + 112, y + 1), 11, (120, 255, 150), True)
            elif p.id != 0 and not g.can_trade(0, p.id):
                self.text(self.screen, f"WAR {int(g.war_left(0, p.id))}s", (x0 + 112, y + 1), 11, (255, 90, 90), True)
            share = 100 * len(p.tiles) / g.land_total
            self.text(self.screen, f"{share:.1f}%", (x0 + 178, y), 13, (255, 240, 180))
        self.text(self.screen, f"Tribes left: {tribes}", (x0 + 8, 30 + len(alive) * 18), 12, (200, 180, 150))

    def draw_messages(self, g):
        y = 8
        for text, when, color in g.messages:
            if g.time - when > 7:
                continue
            img = self.font(14, True).render(text, True, color)
            bg = pygame.Surface((img.get_width() + 12, img.get_height() + 4), pygame.SRCALPHA)
            bg.fill((0, 0, 0, 150))
            self.screen.blit(bg, (8, y))
            self.screen.blit(img, (14, y + 2))
            y += img.get_height() + 8

    def draw_panel(self, g, mouse):
        s = self.screen
        y0 = MAP_H
        pygame.draw.rect(s, (24, 27, 36), (0, y0, WIN_W, PANEL_H))
        pygame.draw.line(s, (70, 80, 100), (0, y0), (WIN_W, y0), 2)
        me = g.players[0]
        mt = g.max_troops(me)

        self.text(s, f"Troops  {fmt(me.troops)} / {fmt(mt)}", (12, y0 + 6), 14, bold=True)
        pygame.draw.rect(s, (50, 55, 70), (12, y0 + 25, 200, 9), border_radius=4)
        pygame.draw.rect(s, me.color, (12, y0 + 25, int(200 * min(1, me.troops / mt)), 9), border_radius=4)
        self.text(s, f"Gold  {fmt(me.gold)}", (12, y0 + 40), 14, (255, 215, 80), True)
        self.text(s, f"Rail +{int(g.train_bonus(0) * 100)}% trains", (self.slider.x + 95, y0 + 66), 13, (230, 190, 140))
        self.text(s, f"Land  {100 * len(me.tiles) / g.land_total:.1f}%  (win at {int(WIN_SHARE * 100)}%)",
                  (12, y0 + 60), 14, (180, 220, 255))

        self.text(s, f"Send {int(g.ratio * 100)}% of troops", (self.slider.x, y0 + 26), 14)
        pygame.draw.rect(s, (60, 66, 84), self.slider, border_radius=4)
        fill = self.slider.copy()
        fill.width = int(self.slider.width * g.ratio)
        pygame.draw.rect(s, (230, 80, 80), fill, border_radius=4)
        pygame.draw.circle(s, (255, 255, 255), (self.slider.x + fill.width, self.slider.centery), 8)
        self.text(s, f"Zoom {self.cam.z / MIN_ZOOM:.1f}x", (self.slider.x, y0 + 66), 13, (160, 200, 255))

        for i, (kind, rect) in enumerate(zip(MODES, self.buttons)):
            active = g.mode == kind
            if kind == "upgrade":
                afford, price = True, "half x Lv"
            else:
                afford, price = me.gold >= COST[kind], fmt(COST[kind])
            hover = rect.collidepoint(mouse)
            bg = (90, 60, 60) if active else (52, 58, 76) if hover else (38, 43, 58)
            pygame.draw.rect(s, bg, rect, border_radius=8)
            pygame.draw.rect(s, (230, 80, 80) if active else (80, 90, 115), rect, 2, border_radius=8)
            col = (255, 255, 255) if afford else (120, 120, 130)
            self.text(s, f"{MODE_KEYS[i]}. {LABEL[kind]}", (rect.centerx, rect.y + 19), 11, col, True, True)
            self.text(s, price, (rect.centerx, rect.y + 39), 12,
                      (255, 215, 80) if afford else (120, 120, 130), False, True)

        self.text(s, "Left-click: attack   Right-click land: boat / alliance menu   Ctrl+Wheel: zoom   "
                     "Right-drag/WASD: move   Wheel: troop %   P: pause   Ctrl+R: restart   "
                     f"Plane +{fmt(PLANE_REWARD)}  Ship +{fmt(PORT_REWARD)}  Train +{fmt(TRAIN_REWARD)}", (12, y0 + 90), 12, (150, 155, 170))

    def draw_overlays(self, g):
        s = self.screen
        big = None
        if g.phase == "spawn":
            big, sub = "Click on land to place your nation", "Ctrl+Wheel to zoom, right-drag to move - pick a spot away from others"
        elif g.phase == "won":
            big, sub = "VICTORY!", "Press R to play again"
        elif g.phase == "lost":
            big, sub = "DEFEATED", "Press R to play again"
        elif g.paused:
            big, sub = "PAUSED", "Press P to continue"
        if big:
            shade = pygame.Surface((MAP_W, 110), pygame.SRCALPHA)
            shade.fill((0, 0, 0, 160))
            s.blit(shade, (0, MAP_H // 2 - 55))
            self.text(s, big, (MAP_W // 2, MAP_H // 2 - 15), 34, (255, 255, 255), True, True)
            self.text(s, sub, (MAP_W // 2, MAP_H // 2 + 25), 16, (200, 200, 210), False, True)


# ---------------- Main loop ----------------
def handle_click(g, r, pos):
    mx, my = pos
    for rect, accept in r.popup_rects:
        if rect.collidepoint(pos):
            g.respond_incoming(accept)
            r.popup_rects = []
            return False
    if r.menu:
        r.menu_click(g, pos)
        return False
    if my >= MAP_H:
        for kind, rect in zip(MODES, r.buttons):
            if rect.collidepoint(pos) and g.phase == "play":
                g.mode = None if g.mode == kind else kind
                return False
        if r.slider.inflate(20, 24).collidepoint(pos):
            set_ratio(g, r, mx)
            return True
        return False

    tx, ty = r.mouse_tile(pos)
    if not (0 <= tx < GW and 0 <= ty < GH):
        return False
    err = None
    if g.phase == "spawn":
        err = g.try_player_spawn(tx, ty)
    elif g.phase == "play":
        if g.mode == "nuke":
            err = g.launch_nuke(0, tx, ty)
        elif g.mode == "upgrade":
            err = g.upgrade(0, g.building_near(0, *r.building_tile(pos)))
        elif g.mode == "warship":
            err = g.build_warship(0, *r.building_tile(pos))
            if not err:
                g.mode = None
        elif g.mode == "jet":
            err = g.build_jet(0, *r.building_tile(pos))
            if not err:
                g.mode = None
        elif g.mode:
            err = g.build(0, g.mode, tx, ty)
            if not err:
                g.mode = None
        elif not g.land[ty][tx]:
            err = "That's water - right-click land across it to send a boat"
        else:
            target = g.owner[ty][tx]
            if target == 0:
                err = "That's your land"
            elif target >= 0 and g.is_ally(0, target):
                err = f"{g.players[target].name} is your ally"
            elif g.borders(0, target):
                err = g.send_attack(0, target, g.ratio)
            else:
                err = "Not your border - right-click that land to send a boat"
    if err:
        g.msg(err, (255, 160, 160))
    return False


def set_ratio(g, r, mx):
    g.ratio = max(0.05, min(1.0, round((mx - r.slider.x) / r.slider.width * 20) / 20))


def main():
    pygame.init()
    screen = pygame.display.set_mode((WIN_W, WIN_H))
    pygame.display.set_caption("OpenFront World")
    clock = pygame.time.Clock()
    screen.fill((15, 17, 24))
    font = pygame.font.SysFont("arial", 28, bold=True)
    img = font.render("Building the world map... (first start takes a few seconds)", True, (255, 255, 255))
    screen.blit(img, img.get_rect(center=(WIN_W // 2, WIN_H // 2)))
    pygame.display.flip()
    pygame.event.pump()
    g = Game()
    r = Renderer(screen)
    dragging = False
    right_down, right_moved, last_mouse = False, 0, (0, 0)
    PAN_SPEED = 700

    while True:
        dt = min(clock.tick(FPS) / 1000, 0.1)
        for e in pygame.event.get():
            if e.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
                dragging = handle_click(g, r, e.pos)
            elif e.type == pygame.MOUSEBUTTONUP and e.button == 1:
                dragging = False
            elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 3:
                right_down, right_moved, last_mouse = True, 0, e.pos
            elif e.type == pygame.MOUSEBUTTONUP and e.button == 3:
                if right_moved < 5:
                    if g.mode:
                        g.mode = None
                    elif r.menu:
                        r.menu = None
                    elif g.phase == "play" and e.pos[1] < MAP_H:
                        r.open_menu(g, e.pos)
                right_down = False
            elif e.type == pygame.MOUSEMOTION:
                if dragging:
                    set_ratio(g, r, e.pos[0])
                elif right_down:
                    dx, dy = e.pos[0] - last_mouse[0], e.pos[1] - last_mouse[1]
                    right_moved += abs(dx) + abs(dy)
                    r.cam.pan(-dx, -dy)
                    last_mouse = e.pos
            elif e.type == pygame.MOUSEWHEEL:
                if pygame.key.get_mods() & pygame.KMOD_CTRL:
                    mx, my = pygame.mouse.get_pos()
                    if my < MAP_H:
                        r.cam.zoom_at(mx, my, 1.15 ** e.y)
                else:
                    g.ratio = max(0.05, min(1.0, round((g.ratio + 0.05 * e.y) * 20) / 20))
            elif e.type == pygame.KEYDOWN:
                ctrl = pygame.key.get_mods() & pygame.KMOD_CTRL
                if e.key == pygame.K_ESCAPE:
                    g.mode = None
                    r.menu = None
                elif e.key == pygame.K_p and g.phase == "play":
                    g.paused = not g.paused
                elif e.key == pygame.K_r and (ctrl or g.phase in ("won", "lost")):
                    g = Game()
                    r.cam = Camera()
                    r.menu = None
                elif e.key in (pygame.K_EQUALS, pygame.K_KP_PLUS):
                    r.cam.zoom_at(MAP_W / 2, MAP_H / 2, 1.25)
                elif e.key in (pygame.K_MINUS, pygame.K_KP_MINUS):
                    r.cam.zoom_at(MAP_W / 2, MAP_H / 2, 0.8)
                elif (pygame.K_1 <= e.key <= pygame.K_9 or e.key in (pygame.K_0, pygame.K_n)) and g.phase == "play":
                    kind = MODES[10 if e.key == pygame.K_n else 9 if e.key == pygame.K_0 else e.key - pygame.K_1]
                    g.mode = None if g.mode == kind else kind

        keys = pygame.key.get_pressed()
        px = (keys[pygame.K_d] or keys[pygame.K_RIGHT]) - (keys[pygame.K_a] or keys[pygame.K_LEFT])
        py = (keys[pygame.K_s] or keys[pygame.K_DOWN]) - (keys[pygame.K_w] or keys[pygame.K_UP])
        if px or py:
            r.cam.pan(px * PAN_SPEED * dt, py * PAN_SPEED * dt)

        g.update(dt)
        r.draw(g, pygame.mouse.get_pos())
        pygame.display.flip()


if __name__ == "__main__":
    main()
