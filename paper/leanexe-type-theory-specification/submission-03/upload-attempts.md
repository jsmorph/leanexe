# Replacement upload

The first upload ran curl through a Python subprocess inside the sandbox.  Curl returned exit status 7 before receiving an HTTP response.  The Python caller raised `CalledProcessError` and did not save the captured curl stderr.  The empty response-header file from that attempt remains local.

The direct curl retry used the existing approved curl prefix outside the sandbox.  It returned HTTP 303 and submission `b778e0a57bba`.  The request omitted the `public` field.  The archive's version-2 record already had public export enabled, and the replacement inherited that setting.  The preserved prior-page and submission-page HTML record the checked controls.  No export setting was changed by this task.
