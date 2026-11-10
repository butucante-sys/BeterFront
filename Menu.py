
import json
import os
import subprocess
import sys
import math
import pygame

BASE = os.path.dirname(os.path.abspath(__file__))
GAME_FILE = os.path.join(BASE, "Game.py")
SETTINGS_FILE = os.path.join(BASE, "settings.json")

W, H = 1100, 700

DIFFICULTIES = ["Easy", "Medium", "Hard", "Impossible"]


class Menu:

    def __init__(self):
        pygame.init()

        pygame.display.set_caption("Beterfront")
        # Keep a fixed 1100x700 design canvas and stretch it (nearest-neighbor)
        # to the actual window size. This resizes buttons/UI cleanly without
        # blur. Fullscreen uses borderless windowed mode at desktop resolution
        # (fills the entire screen, no exclusive mode change / no flash).
        self.window = pygame.display.set_mode((W, H), pygame.RESIZABLE)
        self.screen = pygame.Surface((W, H)).convert()
        self.clock = pygame.time.Clock()
        self.time = 0.0
        self.dt = 1 / 60
        self.animations = {}
        self.particles = [
            [float((i * 137) % W), float((i * 83) % H), 1 + (i % 3), 12 + (i % 18)]
            for i in range(42)
        ]

        self.f_title = pygame.font.SysFont("arial", 76, bold=True)
        self.f_heading = pygame.font.SysFont("arial", 34, bold=True)
        self.f_big = pygame.font.SysFont("arial", 27, bold=True)
        self.f_med = pygame.font.SysFont("arial", 21, bold=True)
        self.f_text = pygame.font.SysFont("arial", 17)
        self.f_small = pygame.font.SysFont("arial", 14)

        self.state = "main"
        self.last_state = self.state
        self.transition_alpha = 0.0
        self.error = ""

        self.username = "Player"
        self.player_tag = "TAG"
        self.editing_field = None

        self.difficulty = "Medium"
        self.bots = 100
        self.tribes = 25       # 0 .. 50 weak NPC tribes
        self.game_speed = 1.0  # 0.5x .. 3.0x

        self.options = {
            "Instant build": False,
            "Infinite gold": False,
            "Infinite troops": False,
        }

        # Settings
        self.music_volume = 70
        self.sfx_volume = 80
        self.fullscreen = False
        self.fps_limit = 60
        self.theme = "dark"

        self.dragging = None  # "bots" | "tribes" | "speed" | None
        self.settings_dragging = None

        self.apply_theme()
        self.load_saved_settings()

    # -------------------------------------------------
    # COORDINATE MAPPING (full stretch)
    # -------------------------------------------------

    def window_to_design(self, pos):
        """Map a window/screen position to the fixed 1100x700 design space
        using simple stretch (fills the entire window, no letterbox)."""
        win_w, win_h = self.window.get_size()
        if win_w <= 0 or win_h <= 0:
            return (0, 0)
        x = pos[0] * W / win_w
        y = pos[1] * H / win_h
        return (int(max(0, min(W - 1, x))), int(max(0, min(H - 1, y))))

    # -------------------------------------------------
    # THEMES
    # -------------------------------------------------

    def apply_theme(self):

        global BG_TOP, BG_BOTTOM
        global PANEL, PANEL_LIGHT, BORDER
        global WHITE, MUTED
        global BLUE, BLUE_LIGHT
        global GREEN, GREEN_LIGHT, RED
        global SEA, LAND

        if self.theme == "dark":

            BG_TOP = (10, 17, 32)
            BG_BOTTOM = (17, 30, 52)

            PANEL = (23, 36, 59)
            PANEL_LIGHT = (39, 56, 85)
            BORDER = (54, 76, 111)

            WHITE = (238, 243, 252)
            MUTED = (137, 156, 185)

            BLUE = (55, 125, 245)
            BLUE_LIGHT = (90, 158, 255)

            GREEN = (43, 190, 115)
            GREEN_LIGHT = (75, 220, 145)

            RED = (220, 75, 85)

            SEA = (20, 53, 91)
            LAND = (74, 139, 91)

        else:

            BG_TOP = (225, 235, 248)
            BG_BOTTOM = (242, 246, 252)

            PANEL = (255, 255, 255)
            PANEL_LIGHT = (226, 234, 245)
            BORDER = (190, 204, 225)

            WHITE = (28, 42, 62)
            MUTED = (105, 121, 145)

            BLUE = (48, 112, 225)
            BLUE_LIGHT = (75, 137, 245)

            GREEN = (35, 165, 100)
            GREEN_LIGHT = (55, 195, 120)

            RED = (210, 65, 75)

            SEA = (120, 173, 215)
            LAND = (80, 150, 95)

    # -------------------------------------------------
    # ANIMATION SYSTEM
    # -------------------------------------------------

    @staticmethod
    def smooth(current, target, speed, dt):
        return current + (target - current) * (1.0 - math.exp(-speed * dt))

    def animated_value(self, key, target, speed=12):
        current = self.animations.get(key, target)
        current = self.smooth(current, target, speed, self.dt)
        self.animations[key] = current
        return current

    def draw_particles(self):
        for i, particle in enumerate(self.particles):
            x, y, radius, drift = particle
            x = (x + math.sin(self.time * 0.35 + i) * 0.12) % W
            y = (y - (8 + drift * 0.35) * self.dt) % H
            particle[0], particle[1] = x, y
            pulse = 0.65 + 0.35 * math.sin(self.time * 1.8 + i)
            if self.theme == "dark":
                # Bright icy-blue particles remain visible against the dark UI.
                base = (105, 180, 255)
            else:
                base = (75, 135, 220)
            strength = 0.72 + pulse * 0.28
            color = tuple(min(255, int(channel * strength)) for channel in base)
            pygame.draw.circle(self.screen, color, (int(x), int(y)), radius)

    def draw_transition(self):
        if self.transition_alpha > 0:
            overlay = pygame.Surface((W, H), pygame.SRCALPHA)
            overlay.fill((0, 0, 0, int(self.transition_alpha)))
            self.screen.blit(overlay, (0, 0))

    # -------------------------------------------------
    # DRAWING HELPERS
    # -------------------------------------------------

    def draw_text(self, text, font, color, pos, center=False):

        surface = font.render(str(text), True, color)
        rect = surface.get_rect()

        if center:
            rect.center = pos
        else:
            rect.topleft = pos

        self.screen.blit(surface, rect)
        return rect

    def rounded(self, surface, color, rect, radius=12):

        pygame.draw.rect(
            surface,
            color,
            rect,
            border_radius=radius
        )

    def panel(self, rect):

        shadow = pygame.Surface(
            (rect.w + 20, rect.h + 20),
            pygame.SRCALPHA
        )

        pygame.draw.rect(
            shadow,
            (0, 0, 0, 45),
            (10, 10, rect.w, rect.h),
            border_radius=18
        )

        shadow_offset = int(2 + math.sin(self.time * 1.5 + rect.x * 0.01) * 1.2)
        self.screen.blit(shadow, (rect.x - 10, rect.y - 5 + shadow_offset))

        self.rounded(self.screen, PANEL, rect, 16)

        pygame.draw.rect(
            self.screen,
            BORDER,
            rect,
            1,
            border_radius=16
        )

    def gradient_background(self):

        for y in range(H):

            t = y / H

            color = tuple(
                int(BG_TOP[i] * (1 - t) + BG_BOTTOM[i] * t)
                for i in range(3)
            )

            pygame.draw.line(
                self.screen,
                color,
                (0, y),
                (W, y)
            )

        grid_color = (
            (19, 31, 49)
            if self.theme == "dark"
            else (220, 228, 239)
        )

        for x in range(0, W, 55):
            pygame.draw.line(
                self.screen,
                grid_color,
                (x, 0),
                (x, H)
            )

        for y in range(0, H, 55):
            pygame.draw.line(
                self.screen,
                grid_color,
                (0, y),
                (W, y)
            )

        t = pygame.time.get_ticks() / 1000

        for i in range(5):

            x = int(100 + i * 240 + math.sin(t + i) * 15)
            y = int(100 + math.cos(t * 0.5 + i) * 35)

            pygame.draw.circle(
                self.screen,
                PANEL_LIGHT,
                (x, y),
                3
            )

    def button(
        self,
        rect,
        label,
        mouse,
        color=None,
        hover=None,
        font=None,
        active=False
    ):

        font = font or self.f_med
        color = color or PANEL_LIGHT
        hover = hover or BLUE

        over = rect.collidepoint(mouse)
        key = ("button", label, rect.x, rect.y)
        amount = self.animated_value(key, 1.0 if over else 0.0, 15)
        scale = 1.0 + amount * 0.045
        draw_rect = rect.inflate(int(rect.w * (scale - 1)), int(rect.h * (scale - 1)))
        draw_rect.center = rect.center
        animated_color = tuple(int(color[i] + (hover[i] - color[i]) * amount) for i in range(3))
        self.rounded(self.screen, animated_color, draw_rect, 11)

        if active:
            pygame.draw.rect(self.screen, BLUE_LIGHT, draw_rect, 2, border_radius=11)

        text_color = (255, 255, 255) if (over or active) else WHITE
        self.draw_text(label, font, text_color, draw_rect.center, center=True)
        return over

    def section_title(self, title, x, y):

        self.draw_text(
            title,
            self.f_med,
            WHITE,
            (x, y)
        )

    # -------------------------------------------------
    # HEADER
    # -------------------------------------------------

    def draw_header_settings(self, mouse):

        rect = pygame.Rect(W - 165, 24, 140, 45)

        self.button(
            rect,
            "SETTINGS",
            mouse,
            PANEL_LIGHT,
            BLUE,
            self.f_small
        )

        return rect

    # -------------------------------------------------
    # WORLD MAP
    # -------------------------------------------------

    def draw_world(self, rect):

        self.rounded(
            self.screen,
            SEA,
            rect,
            12
        )

        x0, y0, w, h = rect

        def P(points):

            return [
                (int(x0 + x * w), int(y0 + y * h))
                for x, y in points
            ]

        grid_color = (
            (27, 69, 105)
            if self.theme == "dark"
            else (105, 155, 190)
        )

        for x in range(rect.x + 20, rect.right, 35):

            pygame.draw.line(
                self.screen,
                grid_color,
                (x, rect.y),
                (x, rect.bottom)
            )

        for y in range(rect.y + 20, rect.bottom, 35):

            pygame.draw.line(
                self.screen,
                grid_color,
                (rect.x, y),
                (rect.right, y)
            )

        continents = [

            # North America
            [
                (.06, .18), (.16, .08), (.27, .11),
                (.36, .22), (.31, .36), (.24, .47),
                (.16, .40), (.10, .29)
            ],

            # South America
            [
                (.25, .51), (.34, .53), (.37, .66),
                (.32, .87), (.28, .94), (.24, .73)
            ],

            # Europe
            [
                (.45, .18), (.53, .13), (.58, .20),
                (.56, .29), (.48, .30)
            ],

            # Africa
            [
                (.46, .34), (.56, .32), (.61, .48),
                (.56, .69), (.51, .80), (.47, .59)
            ],

            # Asia
            [
                (.57, .15), (.72, .09), (.88, .16),
                (.95, .29), (.88, .43), (.74, .47),
                (.63, .37), (.58, .26)
            ],

            # Australia
            [
                (.79, .64), (.89, .60), (.94, .70),
                (.89, .81), (.81, .77)
            ]
        ]

        for points in continents:

            polygon = P(points)

            pygame.draw.polygon(
                self.screen,
                LAND,
                polygon
            )

            pygame.draw.polygon(
                self.screen,
                (105, 170, 112),
                polygon,
                2
            )

        locations = [
            (.21, .25),
            (.51, .22),
            (.54, .45),
            (.75, .28),
            (.85, .70)
        ]

        for x, y in locations:

            pygame.draw.circle(
                self.screen,
                (255, 205, 90),
                (
                    int(x0 + x * w),
                    int(y0 + y * h)
                ),
                3 + int((1 + math.sin(self.time * 3 + x * 10)) * 1.2)
            )

        pygame.draw.rect(
            self.screen,
            BORDER,
            rect,
            2,
            border_radius=12
        )

    # -------------------------------------------------
    # MAIN MENU
    # -------------------------------------------------

    def screen_main(self, mouse, clicks):

        self.draw_text(
            "BETERFRONT",
            self.f_title,
            WHITE,
            (W // 2, 170 + int(math.sin(self.time * 1.6) * 5)),
            center=True
        )

        self.draw_text(
            "CONQUER. EXPAND. DOMINATE.",
            self.f_small,
            BLUE_LIGHT,
            (W // 2, 225),
            center=True
        )

        self.draw_text(
            "A world of strategy awaits.",
            self.f_text,
            MUTED,
            (W // 2, 250),
            center=True
        )

        # Player username field
        username_rect = pygame.Rect(
            W // 2 - 190,
            310,
            245,
            52
        )

        self.rounded(
            self.screen,
            PANEL,
            username_rect,
            10
        )

        pygame.draw.rect(
            self.screen,
            BLUE if self.editing_field == "username" else BORDER,
            username_rect,
            2,
            border_radius=10
        )

        username_display = self.username

        if (
            self.editing_field == "username"
            and pygame.time.get_ticks() % 1000 < 500
        ):
            username_display += "|"

        self.draw_text(
            username_display,
            self.f_med,
            WHITE,
            (username_rect.x + 12, username_rect.y + 14)
        )

        # Player tag field
        tag_rect = pygame.Rect(
            W // 2 + 65,
            310,
            125,
            52
        )

        self.rounded(
            self.screen,
            PANEL,
            tag_rect,
            10
        )

        pygame.draw.rect(
            self.screen,
            BLUE if self.editing_field == "tag" else BORDER,
            tag_rect,
            2,
            border_radius=10
        )

        tag_display = self.player_tag

        if (
            self.editing_field == "tag"
            and pygame.time.get_ticks() % 1000 < 500
        ):
            tag_display += "|"

        self.draw_text(
            tag_display,
            self.f_med,
            BLUE_LIGHT,
            (tag_rect.x + 12, tag_rect.y + 14)
        )

        self.draw_text(
            "PLAYER NAME",
            self.f_small,
            MUTED,
            (username_rect.x, 287)
        )

        self.draw_text(
            "PLAYER TAG",
            self.f_small,
            MUTED,
            (tag_rect.x, 287)
        )

        # Preview
        self.draw_text(
            f"[{self.player_tag}] {self.username}",
            self.f_small,
            MUTED,
            (W // 2, 378),
            center=True
        )

        single = pygame.Rect(
            W // 2 - 190, 405, 380, 60
        )

        help_btn = pygame.Rect(
            W // 2 - 190, 480, 380, 52
        )

        quit_btn = pygame.Rect(
            W // 2 - 190, 546, 380, 52
        )

        self.button(
            single,
            "SINGLE PLAYER",
            mouse,
            BLUE,
            BLUE_LIGHT,
            self.f_big
        )

        self.button(
            help_btn,
            "HOW TO PLAY",
            mouse
        )

        self.button(
            quit_btn,
            "QUIT GAME",
            mouse,
            PANEL_LIGHT,
            RED
        )

        settings_btn = self.draw_header_settings(mouse)

        for click in clicks:

            if settings_btn.collidepoint(click):

                self.editing_field = None
                self.state = "settings"
                continue

            if username_rect.collidepoint(click):

                self.editing_field = "username"
                continue

            if tag_rect.collidepoint(click):

                self.editing_field = "tag"
                continue

            self.editing_field = None

            if single.collidepoint(click):
                self.state = "setup"

            elif help_btn.collidepoint(click):
                self.state = "help"

            elif quit_btn.collidepoint(click):
                self.quit()

        self.draw_text(
            "OPENFRONT | SINGLE PLAYER | v0.4",
            self.f_small,
            MUTED,
            (W // 2, H - 28),
            center=True
        )

    # -------------------------------------------------
    # GAME SETUP
    # -------------------------------------------------

    def screen_setup(self, mouse, clicks, mouse_down):

        self.draw_text(
            "GAME SETUP",
            self.f_heading,
            WHITE,
            (40, 30)
        )

        self.draw_text(
            "Configure your world before starting.",
            self.f_small,
            MUTED,
            (42, 72)
        )

        back = pygame.Rect(W - 145, 30, 105, 42)

        self.button(
            back,
            "BACK",
            mouse,
            PANEL_LIGHT,
            BORDER,
            self.f_small
        )

        map_card = pygame.Rect(40, 115, 470, 450)
        self.panel(map_card)

        self.section_title(
            "SELECT MAP",
            map_card.x + 22,
            map_card.y + 22
        )

        self.draw_text(
            "Available battlefield",
            self.f_small,
            MUTED,
            (map_card.x + 22, map_card.y + 55)
        )

        thumb = pygame.Rect(
            map_card.x + 20,
            map_card.y + 100,
            map_card.w - 40,
            265
        )

        self.draw_world(thumb)

        self.draw_text(
            "WORLD",
            self.f_heading,
            WHITE,
            (map_card.centerx, map_card.y + 395),
            center=True
        )

        self.draw_text(
            "The entire world is your battlefield.",
            self.f_small,
            MUTED,
            (map_card.centerx, map_card.y + 425),
            center=True
        )

        settings = pygame.Rect(535, 115, 525, 450)
        self.panel(settings)

        self.section_title(
            "DIFFICULTY",
            settings.x + 22,
            settings.y + 22
        )

        self.draw_text(
            "Choose the AI difficulty.",
            self.f_small,
            MUTED,
            (settings.x + 22, settings.y + 53)
        )

        diff_width = 110
        diff_gap = 8
        diff_rects = []

        for i, difficulty in enumerate(DIFFICULTIES):

            r = pygame.Rect(
                settings.x + 22 + i * (diff_width + diff_gap),
                settings.y + 85,
                diff_width,
                43
            )

            self.button(
                r,
                difficulty,
                mouse,
                BLUE,
                BLUE_LIGHT,
                self.f_small,
                active=difficulty == self.difficulty
            )

            diff_rects.append((difficulty, r))

        self.section_title(
            "BOT COUNT",
            settings.x + 22,
            settings.y + 140
        )

        self.draw_text(
            f"{self.bots} / 400",
            self.f_med,
            BLUE_LIGHT,
            (settings.right - 100, settings.y + 138)
        )

        slider = pygame.Rect(
            settings.x + 22,
            settings.y + 172,
            settings.w - 44,
            8
        )

        self.rounded(self.screen, PANEL_LIGHT, slider, 5)

        fraction = self.animated_value("bot_slider", self.bots / 400.0, 10)

        fill = pygame.Rect(
            slider.x,
            slider.y,
            int(slider.w * fraction),
            slider.h
        )

        self.rounded(self.screen, BLUE, fill, 5)

        knob_x = int(slider.x + slider.w * fraction)

        pygame.draw.circle(
            self.screen,
            WHITE,
            (knob_x, slider.centery),
            11
        )

        pygame.draw.circle(
            self.screen,
            BLUE,
            (knob_x, slider.centery),
            5
        )

        self.draw_text(
            "0",
            self.f_small,
            MUTED,
            (slider.x, slider.y + 12)
        )

        self.draw_text(
            "400",
            self.f_small,
            MUTED,
            (slider.right - 28, slider.y + 12)
        )

        # ---- TRIBE COUNT ----
        self.section_title(
            "TRIBE COUNT",
            settings.x + 22,
            settings.y + 200
        )

        self.draw_text(
            f"{self.tribes} / 50",
            self.f_med,
            BLUE_LIGHT,
            (settings.right - 90, settings.y + 198)
        )

        tribe_slider = pygame.Rect(
            settings.x + 22,
            settings.y + 232,
            settings.w - 44,
            8
        )

        self.rounded(self.screen, PANEL_LIGHT, tribe_slider, 5)

        tribe_frac = self.animated_value("tribe_slider", self.tribes / 50.0, 10)

        tribe_fill = pygame.Rect(
            tribe_slider.x,
            tribe_slider.y,
            int(tribe_slider.w * tribe_frac),
            tribe_slider.h
        )

        self.rounded(self.screen, BLUE, tribe_fill, 5)

        tribe_knob_x = int(tribe_slider.x + tribe_slider.w * tribe_frac)

        pygame.draw.circle(
            self.screen,
            WHITE,
            (tribe_knob_x, tribe_slider.centery),
            11
        )

        pygame.draw.circle(
            self.screen,
            BLUE,
            (tribe_knob_x, tribe_slider.centery),
            5
        )

        self.draw_text(
            "0",
            self.f_small,
            MUTED,
            (tribe_slider.x, tribe_slider.y + 12)
        )

        self.draw_text(
            "50",
            self.f_small,
            MUTED,
            (tribe_slider.right - 20, tribe_slider.y + 12)
        )

        # ---- GAME SPEED ----
        self.section_title(
            "GAME SPEED",
            settings.x + 22,
            settings.y + 260
        )

        speed_label = f"{self.game_speed:.1f}x"
        self.draw_text(
            speed_label,
            self.f_med,
            BLUE_LIGHT,
            (settings.right - 70, settings.y + 258)
        )

        speed_slider = pygame.Rect(
            settings.x + 22,
            settings.y + 292,
            settings.w - 44,
            8
        )

        self.rounded(self.screen, PANEL_LIGHT, speed_slider, 5)

        # Map 0.5 .. 3.0 → 0 .. 1
        speed_frac = self.animated_value(
            "speed_slider",
            (self.game_speed - 0.5) / 2.5,
            10
        )

        speed_fill = pygame.Rect(
            speed_slider.x,
            speed_slider.y,
            int(speed_slider.w * speed_frac),
            speed_slider.h
        )

        self.rounded(self.screen, BLUE, speed_fill, 5)

        speed_knob_x = int(speed_slider.x + speed_slider.w * speed_frac)

        pygame.draw.circle(
            self.screen,
            WHITE,
            (speed_knob_x, speed_slider.centery),
            11
        )

        pygame.draw.circle(
            self.screen,
            BLUE,
            (speed_knob_x, speed_slider.centery),
            5
        )

        self.draw_text(
            "0.5x",
            self.f_small,
            MUTED,
            (speed_slider.x, speed_slider.y + 12)
        )

        self.draw_text(
            "3.0x",
            self.f_small,
            MUTED,
            (speed_slider.right - 30, speed_slider.y + 12)
        )

        self.section_title(
            "GAME MODIFIERS",
            settings.x + 22,
            settings.y + 322
        )

        toggle_rects = []

        for i, name in enumerate(self.options):

            y = settings.y + 352 + i * 28

            self.draw_text(
                name,
                self.f_text,
                WHITE,
                (settings.x + 22, y + 3)
            )

            switch = pygame.Rect(
                settings.right - 80,
                y,
                55,
                25
            )

            enabled = self.options[name]

            self.draw_toggle(switch, enabled)

            toggle_rects.append((name, switch))

        start = pygame.Rect(
            W // 2 - 180,
            600,
            360,
            65
        )

        self.button(
            start,
            "START GAME",
            mouse,
            GREEN,
            GREEN_LIGHT,
            self.f_big
        )

        if self.error:

            self.draw_text(
                self.error,
                self.f_small,
                RED,
                (W // 2, 680),
                center=True
            )

        if mouse_down and self.dragging == "bots":

            f = (mouse[0] - slider.x) / slider.w

            self.bots = int(
                round(max(0, min(1, f)) * 400 / 5) * 5
            )

        if mouse_down and self.dragging == "tribes":

            f = (mouse[0] - tribe_slider.x) / tribe_slider.w

            self.tribes = int(
                round(max(0, min(1, f)) * 50)
            )

        if mouse_down and self.dragging == "speed":

            f = (mouse[0] - speed_slider.x) / speed_slider.w
            f = max(0.0, min(1.0, f))
            # Snap to 0.1 steps between 0.5 and 3.0
            self.game_speed = round(0.5 + f * 2.5, 1)

        for click in clicks:

            if back.collidepoint(click):

                self.state = "main"
                return

            for difficulty, rect in diff_rects:

                if rect.collidepoint(click):
                    self.difficulty = difficulty

            for name, rect in toggle_rects:

                if rect.collidepoint(click):
                    self.options[name] = not self.options[name]

            slider_hitbox = pygame.Rect(
                slider.x - 12,
                slider.y - 14,
                slider.w + 24,
                slider.h + 28
            )

            if slider_hitbox.collidepoint(click):

                self.dragging = "bots"

                f = (click[0] - slider.x) / slider.w

                self.bots = int(
                    round(max(0, min(1, f)) * 400 / 5) * 5
                )

            tribe_hitbox = pygame.Rect(
                tribe_slider.x - 12,
                tribe_slider.y - 14,
                tribe_slider.w + 24,
                tribe_slider.h + 28
            )

            if tribe_hitbox.collidepoint(click):

                self.dragging = "tribes"

                f = (click[0] - tribe_slider.x) / tribe_slider.w

                self.tribes = int(
                    round(max(0, min(1, f)) * 50)
                )

            speed_hitbox = pygame.Rect(
                speed_slider.x - 12,
                speed_slider.y - 14,
                speed_slider.w + 24,
                speed_slider.h + 28
            )

            if speed_hitbox.collidepoint(click):

                self.dragging = "speed"

                f = max(0.0, min(1.0, (click[0] - speed_slider.x) / speed_slider.w))
                self.game_speed = round(0.5 + f * 2.5, 1)

            if start.collidepoint(click):

                self.start_game()
                return

    # -------------------------------------------------
    # TOGGLES AND SLIDERS
    # -------------------------------------------------

    def draw_toggle(self, rect, enabled):
        key = ("toggle", rect.x, rect.y, rect.w, rect.h)
        amount = self.animated_value(key, 1.0 if enabled else 0.0, 14)
        bg = tuple(int(PANEL_LIGHT[i] + (GREEN[i] - PANEL_LIGHT[i]) * amount) for i in range(3))
        self.rounded(self.screen, bg, rect, 14)
        knob_x = int(rect.x + 13 + (rect.w - 26) * amount)
        pygame.draw.circle(self.screen, WHITE, (knob_x, rect.centery), 9)
        pygame.draw.circle(self.screen, BORDER, (knob_x, rect.centery), 9, 1)

    def draw_slider(self, rect, value):

        self.rounded(
            self.screen,
            PANEL_LIGHT,
            rect,
            5
        )

        shown_value = self.animated_value(("slider", rect.x, rect.y, rect.w), value / 100.0, 12)
        fill_width = int(rect.w * shown_value)

        fill = pygame.Rect(
            rect.x,
            rect.y,
            fill_width,
            rect.h
        )

        self.rounded(
            self.screen,
            BLUE,
            fill,
            5
        )

        knob_x = rect.x + fill_width

        pygame.draw.circle(
            self.screen,
            WHITE,
            (knob_x, rect.centery),
            11
        )

        pygame.draw.circle(
            self.screen,
            BLUE,
            (knob_x, rect.centery),
            5
        )

    # -------------------------------------------------
    # SETTINGS SCREEN
    # -------------------------------------------------

    def screen_settings(self, mouse, clicks):

        self.draw_text(
            "SETTINGS",
            self.f_heading,
            WHITE,
            (W // 2, 65),
            center=True
        )

        self.draw_text(
            "Customize your game experience.",
            self.f_small,
            MUTED,
            (W // 2, 100),
            center=True
        )

        panel = pygame.Rect(270, 125, 560, 475)
        self.panel(panel)

        # Music
        self.draw_text(
            f"MUSIC VOLUME     {self.music_volume}%",
            self.f_med,
            WHITE,
            (panel.x + 35, panel.y + 30)
        )

        music_slider = pygame.Rect(
            panel.x + 35,
            panel.y + 77,
            480,
            8
        )

        self.draw_slider(
            music_slider,
            self.music_volume
        )

        # SFX
        self.draw_text(
            f"SOUND EFFECTS     {self.sfx_volume}%",
            self.f_med,
            WHITE,
            (panel.x + 35, panel.y + 115)
        )

        sfx_slider = pygame.Rect(
            panel.x + 35,
            panel.y + 162,
            480,
            8
        )

        self.draw_slider(
            sfx_slider,
            self.sfx_volume
        )

        # Fullscreen
        self.draw_text(
            "FULLSCREEN",
            self.f_med,
            WHITE,
            (panel.x + 35, panel.y + 200)
        )

        fullscreen_rect = pygame.Rect(
            panel.right - 100,
            panel.y + 196,
            55,
            27
        )

        self.draw_toggle(
            fullscreen_rect,
            self.fullscreen
        )

        # Theme selection
        self.draw_text(
            "APPEARANCE",
            self.f_med,
            WHITE,
            (panel.x + 35, panel.y + 245)
        )

        self.draw_text(
            "Choose your preferred menu theme.",
            self.f_small,
            MUTED,
            (panel.x + 35, panel.y + 275)
        )

        dark_rect = pygame.Rect(
            panel.x + 35,
            panel.y + 305,
            225,
            43
        )

        light_rect = pygame.Rect(
            panel.x + 275,
            panel.y + 305,
            225,
            43
        )

        self.button(
            dark_rect,
            "DARK MODE",
            mouse,
            BLUE if self.theme == "dark" else PANEL_LIGHT,
            BLUE_LIGHT,
            self.f_small,
            active=self.theme == "dark"
        )

        self.button(
            light_rect,
            "LIGHT MODE",
            mouse,
            BLUE if self.theme == "light" else PANEL_LIGHT,
            BLUE_LIGHT,
            self.f_small,
            active=self.theme == "light"
        )

        # FPS
        self.draw_text(
            "FPS LIMIT",
            self.f_med,
            WHITE,
            (panel.x + 35, panel.y + 365)
        )

        fps_values = [30, 60, 120, 0]
        fps_labels = ["30", "60", "120", "UNLIMITED"]

        fps_rects = []

        for i, (value, label) in enumerate(
            zip(fps_values, fps_labels)
        ):

            rect = pygame.Rect(
                panel.x + 35 + i * 120,
                panel.y + 397,
                105,
                42
            )

            self.button(
                rect,
                label,
                mouse,
                BLUE,
                BLUE_LIGHT,
                self.f_small,
                active=self.fps_limit == value
            )

            fps_rects.append((value, rect))

        back = pygame.Rect(
            W // 2 - 100,
            620,
            200,
            45
        )

        self.button(
            back,
            "BACK",
            mouse,
            PANEL_LIGHT,
            BORDER
        )

        # Dragging
        if self.settings_dragging == "music":

            self.music_volume = max(
                0,
                min(
                    100,
                    int(
                        (mouse[0] - music_slider.x)
                        / music_slider.w * 100
                    )
                )
            )

        elif self.settings_dragging == "sfx":

            self.sfx_volume = max(
                0,
                min(
                    100,
                    int(
                        (mouse[0] - sfx_slider.x)
                        / sfx_slider.w * 100
                    )
                )
            )

        # Click handling
        for click in clicks:

            if back.collidepoint(click):

                self.state = "main"
                self.settings_dragging = None
                return

            if music_slider.inflate(0, 25).collidepoint(click):

                self.settings_dragging = "music"

                self.music_volume = max(
                    0,
                    min(
                        100,
                        int(
                            (click[0] - music_slider.x)
                            / music_slider.w * 100
                        )
                    )
                )

            elif sfx_slider.inflate(0, 25).collidepoint(click):

                self.settings_dragging = "sfx"

                self.sfx_volume = max(
                    0,
                    min(
                        100,
                        int(
                            (click[0] - sfx_slider.x)
                            / sfx_slider.w * 100
                        )
                    )
                )

            if fullscreen_rect.collidepoint(click):

                # Use borderless windowed fullscreen (desktop resolution,
                # no exclusive mode change) so there is no black flash and
                # no display-mode switch. This is "fullscreen windowed".
                info = pygame.display.Info()
                if not self.fullscreen:
                    self.window = pygame.display.set_mode(
                        (info.current_w, info.current_h),
                        pygame.NOFRAME
                    )
                    self.fullscreen = True
                else:
                    self.window = pygame.display.set_mode(
                        (W, H),
                        pygame.RESIZABLE
                    )
                    self.fullscreen = False
                # Clear any previous error about fullscreen
                if self.error.startswith("Fullscreen"):
                    self.error = ""

            if dark_rect.collidepoint(click):

                self.theme = "dark"
                self.apply_theme()

            if light_rect.collidepoint(click):

                self.theme = "light"
                self.apply_theme()

            for value, rect in fps_rects:

                if rect.collidepoint(click):
                    self.fps_limit = value

    # -------------------------------------------------
    # HELP SCREEN
    # -------------------------------------------------

    def screen_help(self, mouse, clicks):

        self.draw_text(
            "HOW TO PLAY",
            self.f_heading,
            WHITE,
            (W // 2, 75),
            center=True
        )

        panel = pygame.Rect(145, 130, 810, 440)
        self.panel(panel)

        instructions = [

            ("01", "Choose your starting location",
             "Select a territory on the world map."),

            ("02", "Expand your territory",
             "Attack neighboring land and conquer new regions."),

            ("03", "Manage your troops",
             "Use the attack percentage slider to control your armies."),

            ("04", "Build your economy",
             "Construct cities, ports and defensive structures."),

            ("05", "Cross the oceans",
             "Use boats to reach and attack other continents."),

            ("06", "Conquer the world",
             "Eliminate your enemies and become the last nation standing.")
        ]

        y = panel.y + 35

        for number, title, description in instructions:

            self.rounded(
                self.screen,
                PANEL_LIGHT,
                pygame.Rect(panel.x + 25, y, 48, 48),
                10
            )

            self.draw_text(
                number,
                self.f_med,
                BLUE_LIGHT,
                (panel.x + 49, y + 24),
                center=True
            )

            self.draw_text(
                title,
                self.f_med,
                WHITE,
                (panel.x + 95, y + 2)
            )

            self.draw_text(
                description,
                self.f_small,
                MUTED,
                (panel.x + 95, y + 29)
            )

            y += 65

        back = pygame.Rect(
            W // 2 - 100,
            605,
            200,
            48
        )

        self.button(
            back,
            "BACK",
            mouse,
            PANEL_LIGHT,
            BORDER
        )

        for click in clicks:

            if back.collidepoint(click):
                self.state = "main"

    # -------------------------------------------------
    # SETTINGS DATA
    # -------------------------------------------------

    def load_saved_settings(self):
        """Restore last-used play settings from settings.json if present."""
        if not os.path.isfile(SETTINGS_FILE):
            return
        try:
            with open(SETTINGS_FILE, encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            return
        if data.get("difficulty") in DIFFICULTIES:
            self.difficulty = data["difficulty"]
        try:
            self.bots = max(0, min(400, int(data.get("bots", self.bots))))
        except (TypeError, ValueError):
            pass
        try:
            # Prefer explicit tribes count; fall back to disable_npcs legacy flag
            if "tribes" in data:
                self.tribes = max(0, min(50, int(data["tribes"])))
            elif data.get("disable_npcs"):
                self.tribes = 0
        except (TypeError, ValueError):
            pass
        try:
            self.game_speed = max(0.5, min(3.0, float(data.get("game_speed", 1.0))))
        except (TypeError, ValueError):
            pass
        if "instant_build" in data:
            self.options["Instant build"] = bool(data["instant_build"])
        if "infinite_gold" in data:
            self.options["Infinite gold"] = bool(data["infinite_gold"])
        if "infinite_troops" in data:
            self.options["Infinite troops"] = bool(data["infinite_troops"])
        if data.get("username"):
            self.username = str(data["username"])
        if data.get("player_tag"):
            self.player_tag = str(data["player_tag"])
        try:
            self.music_volume = max(0, min(100, int(data.get("music_volume", self.music_volume))))
            self.sfx_volume = max(0, min(100, int(data.get("sfx_volume", self.sfx_volume))))
            self.fps_limit = max(15, min(240, int(data.get("fps_limit", self.fps_limit))))
        except (TypeError, ValueError):
            pass
        if data.get("theme") in ("dark", "light"):
            self.theme = data["theme"]
            self.apply_theme()
        self.fullscreen = bool(data.get("fullscreen", self.fullscreen))

    def collect_settings(self):

        return {
            "mode": "singleplayer",
            "map": "World",

            "username": self.username.strip() or "Player",
            "player_tag": self.player_tag.strip() or "TAG",

            "display_name": (
                f"[{self.player_tag.strip() or 'TAG'}] "
                f"{self.username.strip() or 'Player'}"
            ),

            "difficulty": self.difficulty,
            "bots": self.bots,
            "tribes": self.tribes,
            "game_speed": round(self.game_speed, 2),

            "disable_npcs": self.tribes <= 0,

            "instant_build":
                self.options["Instant build"],

            "infinite_gold":
                self.options["Infinite gold"],

            "infinite_troops":
                self.options["Infinite troops"],

            "music_volume": self.music_volume,
            "sfx_volume": self.sfx_volume,
            "fullscreen": self.fullscreen,
            "fps_limit": self.fps_limit,
            "theme": self.theme
        }

    # -------------------------------------------------
    # START GAME
    # -------------------------------------------------

    def start_game(self):

        if not os.path.isfile(GAME_FILE):

            self.error = "Game.py not found next to menu.py!"
            return

        settings = self.collect_settings()

        with open(
            SETTINGS_FILE,
            "w",
            encoding="utf-8"
        ) as f:

            json.dump(settings, f, indent=4)

        pygame.quit()

        code = subprocess.call(
            [
                sys.executable,
                GAME_FILE,
                "--settings",
                json.dumps(settings)
            ],
            cwd=BASE
        )

        sys.exit(code)

    def quit(self):

        pygame.quit()
        sys.exit()

    # -------------------------------------------------
    # MAIN LOOP
    # -------------------------------------------------

    def run(self):

        while True:

            self.dt = min(self.clock.get_time() / 1000.0, 0.05)
            self.time += self.dt
            clicks = []

            for event in pygame.event.get():

                if event.type == pygame.QUIT:
                    self.quit()

                elif (
                    event.type == pygame.MOUSEBUTTONDOWN
                    and event.button == 1
                ):

                    clicks.append(self.window_to_design(event.pos))

                elif (
                    event.type == pygame.MOUSEBUTTONUP
                    and event.button == 1
                ):

                    self.dragging = None
                    self.settings_dragging = None

                elif event.type == pygame.KEYDOWN:

                    if event.key == pygame.K_ESCAPE:

                        if self.state != "main":

                            self.state = "main"
                            self.dragging = None
                            self.settings_dragging = None
                            self.editing_field = None

                        else:

                            self.editing_field = None

                    elif (
                        self.state == "main"
                        and self.editing_field is not None
                    ):

                        if event.key == pygame.K_BACKSPACE:

                            if self.editing_field == "username":

                                self.username = self.username[:-1]

                            elif self.editing_field == "tag":

                                self.player_tag = self.player_tag[:-1]

                        elif event.key in (
                            pygame.K_RETURN,
                            pygame.K_KP_ENTER
                        ):

                            self.editing_field = None

                        elif event.unicode.isprintable():

                            if (
                                self.editing_field == "username"
                                and len(self.username) < 16
                            ):

                                self.username += event.unicode

                            elif (
                                self.editing_field == "tag"
                                and len(self.player_tag) < 8
                            ):

                                self.player_tag += event.unicode.upper()

            mouse = self.window_to_design(pygame.mouse.get_pos())
            mouse_down = pygame.mouse.get_pressed()[0]

            self.gradient_background()
            self.draw_particles()

            if self.state == "main":

                self.screen_main(mouse, clicks)

            elif self.state == "setup":

                self.screen_setup(
                    mouse,
                    clicks,
                    mouse_down
                )

            elif self.state == "help":

                self.screen_help(mouse, clicks)

            elif self.state == "settings":

                self.screen_settings(mouse, clicks)

            if self.state != self.last_state:
                self.last_state = self.state
                self.transition_alpha = 155
            self.transition_alpha = max(0.0, self.transition_alpha - 520 * self.dt)
            self.draw_transition()

            # Present the fixed design canvas stretched to fill the entire
            # window (nearest-neighbor). This makes fullscreen truly fill the
            # screen and resizes all buttons/UI cleanly without blur.
            display_size = self.window.get_size()
            if display_size != (W, H):
                frame = pygame.transform.scale(self.screen, display_size)
                self.window.blit(frame, (0, 0))
            else:
                self.window.blit(self.screen, (0, 0))
            pygame.display.flip()

            fps = self.fps_limit if self.fps_limit > 0 else 0
            self.clock.tick(fps)


if __name__ == "__main__":
    Menu().run()
