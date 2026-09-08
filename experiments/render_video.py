"""Start site with npm run dev; pip install playwright; playwright install chromium.
Usage: python3 experiments/render_video.py http://127.0.0.1:4175/film.html
Requires ffmpeg on PATH. Frames are rendered at deterministic simulation times.
"""
from pathlib import Path
from playwright.sync_api import sync_playwright
import subprocess,tempfile,sys,json,os
root=Path(__file__).resolve().parents[1]
url=sys.argv[1] if len(sys.argv)>1 else 'http://127.0.0.1:5173/film.html'
with sync_playwright() as p, tempfile.TemporaryDirectory(prefix='pinwheel-frames-') as tmp:
    opts={'headless':True,'args':['--enable-unsafe-swiftshader']}
    if os.environ.get('PINWHEEL_CHROME'):opts['executable_path']=os.environ['PINWHEEL_CHROME']
    browser=p.chromium.launch(**opts)
    page=browser.new_page(viewport={'width':1600,'height':900},device_scale_factor=1)
    errors=[];page.on('pageerror',lambda e:errors.append(str(e)))
    page.goto(url+('\u0026' if '?' in url else '?')+'capture=1',wait_until='networkidle');page.wait_for_function('window.visualReady');page.evaluate('document.fonts.ready')
    for frame in range(432):
        page.evaluate('(t)=>window.renderAt(t)',frame/24)
        page.screenshot(path=f'{tmp}/{frame:04d}.png',animations='disabled')
        if frame==48:page.screenshot(path=str(root/'media/preview.png'))
        if frame%72==0:print('Rendered',frame,'/ 432',flush=True)
    assert not errors,errors
    browser.close()
    subprocess.run(['ffmpeg','-y','-loglevel','error','-framerate','24','-i',f'{tmp}/%04d.png','-c:v','libx264','-crf','18','-preset','medium','-pix_fmt','yuv420p','-movflags','+faststart',str(root/'media/four-real-periods.mp4')],check=True)
(root/'results/video-verification.json').write_text(json.dumps({'frames':432,'fps':24,'seconds':18,'width':1600,'height':900,'browser_errors':errors},indent=2))
print('Video complete.',flush=True)
