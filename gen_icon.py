#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""生成蓝奏云批量上传工具的图标(.icns) 与 内嵌 base64 PNG。
仅用于构建资源，运行时不依赖 Pillow。"""
import os
import io
import base64
import subprocess

from PIL import Image, ImageDraw, ImageFilter

HERE = os.path.dirname(os.path.abspath(__file__))

SIZE = 1024


def rounded_rect(draw, box, radius, fill):
    draw.rounded_rectangle(box, radius=radius, fill=fill)


def vertical_gradient(size, top, bottom):
    """生成纵向蓝色渐变背景图。size 为整数边长。"""
    w = h = size
    img = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    top_c = tuple(top)
    bot_c = tuple(bottom)
    px = img.load()
    for y in range(h):
        t = y / (h - 1)
        c = tuple(int(top_c[i] + (bot_c[i] - top_c[i]) * t) for i in range(3)) + (255,)
        for x in range(w):
            px[x, y] = c
    return img


def draw_cloud(draw, cx, cy, scale, color):
    """在 (cx,cy) 处绘制一朵云(由若干圆/椭圆组成)。scale 为整体半径基准。"""
    blobs = [
        (-0.62, 0.18, 0.52),
        (-0.18, -0.22, 0.66),
        (0.30, -0.10, 0.58),
        (0.62, 0.20, 0.46),
        (0.0, 0.30, 0.72),
    ]
    for dx, dy, r in blobs:
        x = cx + dx * scale
        y = cy + dy * scale
        rr = r * scale
        draw.ellipse([x - rr, y - rr, x + rr, y + rr], fill=color)


def make_icon(size):
    img = vertical_gradient(size, (64, 156, 255), (30, 110, 230))
    draw = ImageDraw.Draw(img)

    # 圆角背景（让四角透明，符合 macOS 图标风格）
    mask = Image.new("L", (size, size), 0)
    ImageDraw.Draw(mask).rounded_rectangle([0, 0, size, size], radius=int(size * 0.22), fill=255)
    img.putalpha(mask)

    s = size / 1024.0
    # 云（白）
    draw_cloud(draw, cx=size * 0.5, cy=size * 0.62, scale=size * 0.30, color=(255, 255, 255, 255))

    # 向上箭头（蓝）叠加在云上
    aw = size * 0.13          # 箭头杆宽
    ax = size * 0.5
    top_y = size * 0.20
    bot_y = size * 0.60
    head_w = size * 0.20      # 箭头头部半宽
    head_h = size * 0.16
    blue = (38, 120, 225, 255)
    # 杆
    draw.rectangle([ax - aw / 2, top_y + head_h, ax + aw / 2, bot_y], fill=blue)
    # 箭头头部（三角形）
    draw.polygon([
        (ax, top_y),
        (ax - head_w, top_y + head_h),
        (ax + head_w, top_y + head_h),
    ], fill=blue)
    img = img.filter(ImageFilter.GaussianBlur(0))  # 占位，保留平滑
    return img


def main():
    os.makedirs(os.path.join(HERE, "assets"), exist_ok=True)
    iconset = os.path.join(HERE, "assets", "AppIcon.iconset")
    os.makedirs(iconset, exist_ok=True)

    big = make_icon(SIZE)
    # macOS 需要的尺寸
    sizes = {
        "16": 16, "32": 32, "64": 64, "128": 128,
        "256": 256, "512": 512, "1024": 1024,
    }
    for name, px in sizes.items():
        im = big.resize((px, px), Image.LANCZOS)
        im.save(os.path.join(iconset, f"icon_{name}x{name}.png"))
        if px <= 512:
            im.save(os.path.join(iconset, f"icon_{px}x{px}@2x.png"))  # 2x 版本

    icns = os.path.join(HERE, "assets", "app.icns")
    subprocess.run(["iconutil", "--convert", "icns", "--output", icns, iconset], check=True)
    print("icns:", icns)

    # 导出 256x256 的 base64 供脚本内嵌（窗口 iconphoto 用）
    small = big.resize((256, 256), Image.LANCZOS)
    buf = io.BytesIO()
    small.save(buf, format="PNG")
    b64 = base64.b64encode(buf.getvalue()).decode("ascii")
    out = os.path.join(HERE, "assets", "icon_b64.txt")
    with open(out, "w") as f:
        f.write(b64)
    print("base64 len:", len(b64), "->", out)


if __name__ == "__main__":
    main()
