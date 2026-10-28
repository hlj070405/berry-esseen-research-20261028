"""2026-10-28: Transfer the existing private Release asset to a Zenodo draft.

Prepared for a separately authorized temporary GitHub Actions run. No publishing,
no research computations, no stored credentials, and no new research snapshot.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import urllib.error
import urllib.request

REPOSITORY = 'hlj070405/berry-esseen-research-20261028'
ASSET_ID = 684628678
EXPECTED_BYTES = 2010270034
FILE_NAME = 'berry-esseen-review-materials-20261028.zip'
DRAFT = 'https://zenodo.org/api/records/23734685/draft'
ZENODO_TOKEN = os.environ.pop('ZENODO_REVIEW_UPLOAD_TOKEN')
GITHUB_TOKEN = os.environ.pop('GH_REVIEW_READ_TOKEN')


def api(url, method='GET', data=None):
    if not url.startswith('https://zenodo.org/api/records/23734685/'):
        raise RuntimeError('Refusing a different Zenodo destination.')
    body = None if data is None else json.dumps(data).encode()
    headers = {'Authorization': 'Bearer ' + ZENODO_TOKEN,
               'Accept': 'application/vnd.inveniordm.v1+json'}
    if body is not None:
        headers['Content-Type'] = 'application/json'
    with urllib.request.urlopen(urllib.request.Request(
            url, data=body, headers=headers, method=method), timeout=90) as response:
        body = response.read()
    return json.loads(body) if body else None


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


def download_release(target):
    url = f'https://api.github.com/repos/{REPOSITORY}/releases/assets/{ASSET_ID}'
    headers = {'Authorization': 'Bearer ' + GITHUB_TOKEN,
               'Accept': 'application/octet-stream',
               'User-Agent': 'Private-Zenodo-Review-Transfer'}
    try:
        response = urllib.request.build_opener(NoRedirect).open(
            urllib.request.Request(url, headers=headers), timeout=90)
    except urllib.error.HTTPError as error:
        if error.code not in (301, 302, 303, 307, 308):
            raise
        destination = error.headers['Location']
        if not destination.startswith('https://'):
            raise RuntimeError('The asset download did not redirect to HTTPS.')
        # Never forward the GitHub token to the asset storage host.
        response = urllib.request.urlopen(destination, timeout=90)
    with response, target.open('xb') as output:
        shutil.copyfileobj(response, output, 1024 * 1024)
    if target.stat().st_size != EXPECTED_BYTES:
        raise RuntimeError('The private Release asset has an unexpected size.')
    print(json.dumps({'release_asset_downloaded': True,
                      'bytes': target.stat().st_size}), flush=True)


def main():
    record = api(DRAFT)
    if record.get('is_published') is not False or record.get('status') != 'draft':
        raise RuntimeError('The target is not an unpublished draft.')
    if record.get('access', {}).get('files') != 'restricted':
        raise RuntimeError('The target file access is no longer restricted.')
    files_url = record['links']['files']
    entries = api(files_url)['entries']
    complete = next((entry for entry in entries if entry['key'] == FILE_NAME
                     and entry['status'] == 'completed'
                     and entry.get('size') == EXPECTED_BYTES), None)
    if complete is None:
        local_file = Path(FILE_NAME)
        download_release(local_file)
        # These are interrupted, empty transport slots from this same upload task.
        old_names = {'companions-20261028T102820Z.zip',
                     'companions-20261028T102820Z.zip.001',
                     'berry-esseen-companions-20261028.zip', FILE_NAME}
        for entry in entries:
            if (entry['key'] in old_names and entry['status'] == 'pending'
                    and not entry.get('size')):
                api(entry['links']['self'], method='DELETE')
        initialized = api(files_url, method='POST', data=[{'key': FILE_NAME}])
        entry = next(e for e in initialized['entries'] if e['key'] == FILE_NAME)
        destination = entry['links']['content']
        if not destination.startswith(DRAFT + '/files/'):
            raise RuntimeError('Unexpected upload URL.')
        response_file = Path('zenodo-upload-response.json')
        command = ['curl', '--config', '-', '--upload-file', str(local_file),
                   '--url', destination, '--output', str(response_file),
                   '--write-out', '%{http_code}', '--fail-with-body',
                   '--connect-timeout', '30', '--expect100-timeout', '5']
        configuration = ('header = "Authorization: Bearer ' + ZENODO_TOKEN + '"\n'
            'header = "Content-Type: application/octet-stream"\n'
            'header = "Accept: application/json"\n'
            'header = "Expect: 100-continue"\n')
        result = subprocess.run(command, input=configuration, text=True,
                                stdout=subprocess.PIPE, check=False)
        if result.returncode or result.stdout.strip() not in ('200', '201'):
            raise RuntimeError(f'curl exited {result.returncode}; HTTP {result.stdout.strip()}')
        committed = api(entry['links']['commit'], method='POST')
        if committed.get('status') != 'completed' or committed.get('size') != EXPECTED_BYTES:
            raise RuntimeError('The full archive was not committed by Zenodo.')
    actual = {e['key']: e for e in api(files_url)['entries']}
    expected = {'berry-esseen-manuscript-20261028.pdf': 299439,
                'berry-esseen-sources-20261028.zip': 713234,
                FILE_NAME: EXPECTED_BYTES}
    for name, size in expected.items():
        if (actual.get(name, {}).get('size') != size
                or actual[name].get('status') != 'completed'):
            raise RuntimeError('An expected review file is incomplete: ' + name)
    if api(DRAFT).get('is_published') is not False:
        raise RuntimeError('Unexpected publication-state change.')
    print(json.dumps({'complete': True, 'published': False,
                      'files': expected}), flush=True)


if __name__ == '__main__':
    main()
