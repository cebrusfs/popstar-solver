#!/usr/bin/env python
import sys

from PIL import Image, ImageFilter

if len(sys.argv) > 1:
    path = sys.argv[1]
else:
    #path = './IMG_4990.PNG'
    path = './2017-05-11.jpg'

sizedict = {
    (640, 1136): {
        'crop_hight': 498,
        'width': 64,
    },
    (750, 1334): {
        'crop_hight': 584,
        'width': 75,
    },
}



im = Image.open(path)
setting = sizedict[im.size]

im = im.crop((0, setting['crop_hight'], im.size[0], im.size[1]))
#im.save("test.bmp")

mp = []
width = setting['width']
offset = width / 2

rules = {
    # r, g, b
    (200, None, 200): 'p',
    (200, -100, -100): 'r',
    (150, 100, -100): 'y',
    (-50, 200, -50): 'g',
    (-100, 100, 200): 'b',
}

def check(rule, color):
    #print rule, color
    for r, c in zip(rule, color):
        if r is None: continue

        rr = abs(r)
        if r > 0 and not c > rr:
            return False
        if r < 0 and not c < rr:
            return False

    #print 'good'
    return True


for i in range(10):
    s = ''
    for j in range(10):
        xy = (width * j + offset, width * i + offset)
        c = im.getpixel(xy)

        result = [val for rule, val in rules.items() if check(rule, c)]

        if not result or len(result) > 1:
            print i, j, c, result
            assert False

        s += result[0]
        #print c,
    mp.append(s)
    #print ''

print '\n'.join(mp)
